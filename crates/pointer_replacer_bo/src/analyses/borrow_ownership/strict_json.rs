//! JSON transport boundary: duplicate object keys must not be normalized away.

use serde::{
    Deserialize,
    de::{self, MapAccess, SeqAccess, Visitor},
};
use serde_json::{Map, Number, Value};

pub(crate) fn parse(bytes: &[u8]) -> Result<Value, String> {
    let mut deserializer = serde_json::Deserializer::from_slice(bytes);
    let value = UniqueValue::deserialize(&mut deserializer).map_err(|error| error.to_string())?;
    deserializer.end().map_err(|error| error.to_string())?;
    Ok(value.0)
}

/// Validates one strict JSON value without retaining its values.
pub(crate) fn validate_reader<R: std::io::Read>(reader: R) -> Result<(), String> {
    let mut deserializer = serde_json::Deserializer::from_reader(reader);
    Discard::deserialize(&mut deserializer).map_err(|error| error.to_string())?;
    deserializer.end().map_err(|error| error.to_string())
}

/// Discards values while retaining each open object's decoded keys for the
/// duplicate check. Arrays do not accumulate elements; each value is consumed
/// before the next. The deserializer's native recursion limit remains active.
pub(crate) struct Discard;

impl<'de> Deserialize<'de> for Discard {
    fn deserialize<D: de::Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        deserializer.deserialize_any(Self)
    }
}

impl<'de> Visitor<'de> for Discard {
    type Value = Self;

    fn expecting(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter.write_str("a JSON value with unique object keys")
    }

    fn visit_unit<E: de::Error>(self) -> Result<Self::Value, E> {
        Ok(Self)
    }

    fn visit_bool<E: de::Error>(self, _value: bool) -> Result<Self::Value, E> {
        Ok(Self)
    }

    fn visit_i64<E: de::Error>(self, _value: i64) -> Result<Self::Value, E> {
        Ok(Self)
    }

    fn visit_u64<E: de::Error>(self, _value: u64) -> Result<Self::Value, E> {
        Ok(Self)
    }

    fn visit_f64<E: de::Error>(self, value: f64) -> Result<Self::Value, E> {
        if value.is_finite() {
            Ok(Self)
        } else {
            Err(E::custom("nonfinite JSON number"))
        }
    }

    fn visit_str<E: de::Error>(self, _value: &str) -> Result<Self::Value, E> {
        Ok(Self)
    }

    fn visit_string<E: de::Error>(self, _value: String) -> Result<Self::Value, E> {
        Ok(Self)
    }

    fn visit_seq<A: SeqAccess<'de>>(self, mut sequence: A) -> Result<Self::Value, A::Error> {
        while sequence.next_element::<Self>()?.is_some() {}
        Ok(Self)
    }

    fn visit_map<A: MapAccess<'de>>(self, mut object: A) -> Result<Self::Value, A::Error> {
        let mut keys = std::collections::BTreeSet::new();
        while let Some(key) = object.next_key::<String>()? {
            if keys.contains(&key) {
                return Err(de::Error::custom(format!(
                    "duplicate JSON object key: {key:?}"
                )));
            }
            keys.insert(key);
            object.next_value::<Self>()?;
        }
        Ok(Self)
    }
}

/// Recursion uses this visitor for every value, including objects in arrays.
/// Object keys are decoded before comparison, so escaped spellings of one key
/// cannot bypass the check. The existing JSON recursion limit remains active.
pub(crate) struct UniqueValue(pub(crate) Value);

impl<'de> Deserialize<'de> for UniqueValue {
    fn deserialize<D: de::Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        deserializer.deserialize_any(UniqueVisitor)
    }
}

struct UniqueVisitor;
impl<'de> Visitor<'de> for UniqueVisitor {
    type Value = UniqueValue;

    fn expecting(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter.write_str("a JSON value with unique object keys")
    }

    fn visit_unit<E: de::Error>(self) -> Result<Self::Value, E> {
        Ok(UniqueValue(Value::Null))
    }

    fn visit_bool<E: de::Error>(self, value: bool) -> Result<Self::Value, E> {
        Ok(UniqueValue(Value::Bool(value)))
    }

    fn visit_i64<E: de::Error>(self, value: i64) -> Result<Self::Value, E> {
        Ok(UniqueValue(Value::Number(Number::from(value))))
    }

    fn visit_u64<E: de::Error>(self, value: u64) -> Result<Self::Value, E> {
        Ok(UniqueValue(Value::Number(Number::from(value))))
    }

    fn visit_f64<E: de::Error>(self, value: f64) -> Result<Self::Value, E> {
        Number::from_f64(value)
            .map(|number| UniqueValue(Value::Number(number)))
            .ok_or_else(|| E::custom("nonfinite JSON number"))
    }

    fn visit_str<E: de::Error>(self, value: &str) -> Result<Self::Value, E> {
        Ok(UniqueValue(Value::String(value.to_owned())))
    }

    fn visit_string<E: de::Error>(self, value: String) -> Result<Self::Value, E> {
        Ok(UniqueValue(Value::String(value)))
    }

    fn visit_seq<A: SeqAccess<'de>>(self, mut sequence: A) -> Result<Self::Value, A::Error> {
        let mut values = Vec::new();
        while let Some(value) = sequence.next_element::<UniqueValue>()? {
            values.push(value.0);
        }
        Ok(UniqueValue(Value::Array(values)))
    }

    fn visit_map<A: MapAccess<'de>>(self, mut object: A) -> Result<Self::Value, A::Error> {
        let mut values = Map::new();
        while let Some(key) = object.next_key::<String>()? {
            if values.contains_key(&key) {
                return Err(de::Error::custom(format!(
                    "duplicate JSON object key: {key:?}"
                )));
            }
            let value = object.next_value::<UniqueValue>()?;
            values.insert(key, value.0);
        }
        Ok(UniqueValue(Value::Object(values)))
    }
}

#[cfg(test)]
mod tests {
    use serde_json::json;

    use super::parse;

    #[test]
    fn e5_i_strict_json_rejects_duplicate_root_keys_even_with_equal_values() {
        for bytes in [
            br#"{"schema":"era5a","schema":"era5a"}"#.as_slice(),
            br#"{"schema":"era4","schema":"era5a"}"#.as_slice(),
            // Escapes do not create a different decoded object key.
            br#"{"schema":1,"\u0073chema":1}"#.as_slice(),
        ] {
            assert!(parse(bytes).is_err(), "duplicate root key: {:?}", bytes);
        }
    }

    #[test]
    fn e5_i_strict_json_rejects_nested_duplicates_and_duplicate_plus_missing() {
        for bytes in [
            br#"{"payload":{"value":true,"value":true}}"#.as_slice(),
            br#"{"rows":[{"slot":"p","slot":"q"}]}"#.as_slice(),
            // Repeating one required family cannot substitute for another
            // missing family, even when a map collector would keep one value.
            br#"{"families":{"loans":[],"loans":[]}}"#.as_slice(),
        ] {
            assert!(parse(bytes).is_err(), "nested duplicate key: {:?}", bytes);
        }
    }

    #[test]
    fn e5_i_strict_json_preserves_valid_values_arrays_and_object_scopes() {
        let bytes = br#"{
            "null":null,"false":false,"true":true,
            "integer":42,"negative":-7,"fraction":1.25,
            "text":"line\n\u03bb","empty_object":{},"empty_array":[],
            "rows":[{"slot":"p"},{"slot":"q"}],
            "nested":{"slot":"r","array":[null,false,3,"s",[4]]}
        }"#;
        assert_eq!(
            parse(bytes).unwrap(),
            json!({
                "null":null,"false":false,"true":true,
                "integer":42,"negative":-7,"fraction":1.25,
                "text":"line\nλ","empty_object":{},"empty_array":[],
                "rows":[{"slot":"p"},{"slot":"q"}],
                "nested":{"slot":"r","array":[null,false,3,"s",[4]]}
            })
        );
        // JSON still has exactly one top-level value.
        assert!(parse(br#"{} {}"#).is_err());
        assert!(parse(br#"{"value":}"#).is_err());
    }

    struct ErrorAfterPrefix(std::io::Cursor<&'static [u8]>);

    impl std::io::Read for ErrorAfterPrefix {
        fn read(&mut self, buffer: &mut [u8]) -> std::io::Result<usize> {
            if self.0.position() == self.0.get_ref().len() as u64 {
                return Err(std::io::Error::other("late reader fault"));
            }
            std::io::Read::read(&mut self.0, buffer)
        }
    }

    #[test]
    fn r281_strict_reader_rejects_duplicate_before_reading_a_faulting_tail() {
        let reader = ErrorAfterPrefix(std::io::Cursor::new(br#"{"key":1,"\u006bey":"#.as_slice()));
        let error = super::validate_reader(reader).unwrap_err();
        assert!(
            error.contains("duplicate JSON object key"),
            "strict traversal must reject the decoded duplicate before requesting the tail: {error}"
        );
        assert!(!error.contains("late reader fault"));
    }

    #[test]
    fn r281_strict_reader_accepts_large_arrays_and_independent_object_scopes() {
        let mut bytes = Vec::from(br#"{"rows":["#.as_slice());
        for index in 0..32_768 {
            if index != 0 {
                bytes.push(b',');
            }
            bytes.extend_from_slice(br#"{"key":[null,true,false,-7,1.25,"\u03bb"]}"#);
        }
        bytes.extend_from_slice(b"]}");
        super::validate_reader(bytes.as_slice()).unwrap();
    }

    #[test]
    fn r281_strict_reader_rejects_decoded_duplicates_at_every_nesting_shape() {
        for bytes in [
            br#"{"key":1,"key":1}"#.as_slice(),
            br#"{"key":1,"\u006bey":1}"#.as_slice(),
            br#"{"outer":{"key":1,"key":2}}"#.as_slice(),
            br#"[{"rows":[{"key":1,"\u006bey":2}]}]"#.as_slice(),
        ] {
            let error = super::validate_reader(bytes).unwrap_err();
            assert!(error.contains("duplicate JSON object key"), "{error}");
        }
    }

    #[test]
    fn r281_strict_reader_preserves_syntax_trailing_and_recursion_checks() {
        for bytes in [
            b"{} {}".as_slice(),
            b"null trailing".as_slice(),
            b"{\"value\":}".as_slice(),
            b"[1,]".as_slice(),
            b"1e999".as_slice(),
        ] {
            assert!(super::validate_reader(bytes).is_err(), "{bytes:?}");
        }
        let nested = format!("{}0{}", "[".repeat(128), "]".repeat(128));
        let error = super::validate_reader(nested.as_bytes()).unwrap_err();
        assert!(error.contains("recursion limit exceeded"), "{error}");
        super::validate_reader(b" [null,{},[]] \n".as_slice()).unwrap();
    }

    #[test]
    fn r281_strict_reader_propagates_reader_failure_without_a_prior_json_error() {
        let reader = ErrorAfterPrefix(std::io::Cursor::new(b"[0,".as_slice()));
        let error = super::validate_reader(reader).unwrap_err();
        assert!(error.contains("late reader fault"), "{error}");
    }
}
