use std::collections::BTreeMap;

use syn::visit::{self, Visit};

const STATISTIC_KEYS: [&str; 9] = [
    "num_unsafe_ptrs",
    "num_non_arr_unsafe_ptrs",
    "num_mut_unsafe_ptrs",
    "num_non_arr_mut_unsafe_ptrs",
    "num_unsafe_usages",
    "num_non_arr_unsafe_usages",
    "num_mut_unsafe_usages",
    "num_non_arr_mut_unsafe_usages",
    "num_owning_ptrs_detected",
];

#[derive(Debug, Default, PartialEq, Eq)]
pub struct TypePositionCounts {
    pub local_box: u64,
    pub local_option_box: u64,
    pub param_box: u64,
    pub param_option_box: u64,
    pub return_box: u64,
    pub return_option_box: u64,
    pub field_box: u64,
    pub field_option_box: u64,
}

#[derive(Debug, Default, PartialEq, Eq)]
pub struct RustCounts {
    pub types: TypePositionCounts,
    pub box_new_calls: u64,
    pub box_from_raw_calls: u64,
    pub box_into_raw_calls: u64,
    pub malloc_calls: u64,
    pub calloc_calls: u64,
    pub realloc_calls: u64,
    pub free_calls: u64,
    pub drop_calls: u64,
}

impl RustCounts {
    pub fn merge(&mut self, other: Self) {
        self.types.local_box += other.types.local_box;
        self.types.local_option_box += other.types.local_option_box;
        self.types.param_box += other.types.param_box;
        self.types.param_option_box += other.types.param_option_box;
        self.types.return_box += other.types.return_box;
        self.types.return_option_box += other.types.return_option_box;
        self.types.field_box += other.types.field_box;
        self.types.field_option_box += other.types.field_option_box;
        self.box_new_calls += other.box_new_calls;
        self.box_from_raw_calls += other.box_from_raw_calls;
        self.box_into_raw_calls += other.box_into_raw_calls;
        self.malloc_calls += other.malloc_calls;
        self.calloc_calls += other.calloc_calls;
        self.realloc_calls += other.realloc_calls;
        self.free_calls += other.free_calls;
        self.drop_calls += other.drop_calls;
    }

    pub fn box_type_positions(&self) -> u64 {
        self.types.local_box
            + self.types.local_option_box
            + self.types.param_box
            + self.types.param_option_box
            + self.types.return_box
            + self.types.return_option_box
            + self.types.field_box
            + self.types.field_option_box
    }

    pub fn allocation_calls(&self) -> u64 {
        self.malloc_calls + self.calloc_calls + self.realloc_calls
    }
}

#[derive(Debug, Default, PartialEq, Eq)]
pub struct JsonClaimCounts {
    pub ownership_fn: BTreeMap<String, u64>,
    pub ownership_struct: BTreeMap<String, u64>,
    pub ownership_fn_by_depth: Vec<BTreeMap<String, u64>>,
    pub ownership_struct_by_depth: Vec<BTreeMap<String, u64>>,
    pub mutability_fn: BTreeMap<String, u64>,
    pub mutability_struct: BTreeMap<String, u64>,
    pub mutability_fn_by_depth: Vec<BTreeMap<String, u64>>,
    pub mutability_struct_by_depth: Vec<BTreeMap<String, u64>>,
    pub fatness_fn: BTreeMap<String, u64>,
    pub fatness_struct: BTreeMap<String, u64>,
    pub fatness_fn_by_depth: Vec<BTreeMap<String, u64>>,
    pub fatness_struct_by_depth: Vec<BTreeMap<String, u64>>,
    pub statistics: BTreeMap<String, u64>,
    pub max_depth: usize,
}

pub fn analyze_rust_source(source: &str) -> Result<RustCounts, syn::Error> {
    let file = syn::parse_file(source)?;
    let mut visitor = RustInventoryVisitor::default();
    visitor.visit_file(&file);
    Ok(visitor.counts)
}

pub fn analyze_json_claims(
    ownership: &str,
    statistics: &str,
    mutability: &str,
    fatness: &str,
) -> Result<JsonClaimCounts, String> {
    let ownership = parse_json_document("ownership.json", ownership)?;
    let statistics = parse_json_document("statistics.json", statistics)?;
    let mutability = parse_json_document("mutability.json", mutability)?;
    let fatness = parse_json_document("fatness.json", fatness)?;

    let mut counts = JsonClaimCounts::default();
    count_qualifier_scope(
        "ownership.json",
        &ownership,
        "fn_data",
        &["Owning", "Transient", "Unknown"],
        &mut counts.ownership_fn,
        &mut counts.ownership_fn_by_depth,
        &mut counts.max_depth,
    )?;
    count_qualifier_scope(
        "ownership.json",
        &ownership,
        "struct_data",
        &["Owning", "Transient", "Unknown"],
        &mut counts.ownership_struct,
        &mut counts.ownership_struct_by_depth,
        &mut counts.max_depth,
    )?;
    count_qualifier_scope(
        "mutability.json",
        &mutability,
        "fn_data",
        &["Mut", "Imm"],
        &mut counts.mutability_fn,
        &mut counts.mutability_fn_by_depth,
        &mut counts.max_depth,
    )?;
    count_qualifier_scope(
        "mutability.json",
        &mutability,
        "struct_data",
        &["Mut", "Imm"],
        &mut counts.mutability_struct,
        &mut counts.mutability_struct_by_depth,
        &mut counts.max_depth,
    )?;
    count_qualifier_scope(
        "fatness.json",
        &fatness,
        "fn_data",
        &["Arr", "Ptr"],
        &mut counts.fatness_fn,
        &mut counts.fatness_fn_by_depth,
        &mut counts.max_depth,
    )?;
    count_qualifier_scope(
        "fatness.json",
        &fatness,
        "struct_data",
        &["Arr", "Ptr"],
        &mut counts.fatness_struct,
        &mut counts.fatness_struct_by_depth,
        &mut counts.max_depth,
    )?;
    let statistics = statistics
        .as_object()
        .ok_or_else(|| "statistics.json: root must be an object".to_owned())?;
    for key in STATISTIC_KEYS {
        let value = statistics
            .get(key)
            .ok_or_else(|| format!("statistics.json: missing {key}"))?
            .as_u64()
            .ok_or_else(|| format!("statistics.json: {key} must be a non-negative integer"))?;
        counts.statistics.insert(key.to_owned(), value);
    }
    if let Some(unexpected) = statistics
        .keys()
        .find(|key| !STATISTIC_KEYS.contains(&key.as_str()))
    {
        return Err(format!(
            "statistics.json: unexpected summary counter {unexpected}"
        ));
    }
    Ok(counts)
}

#[derive(Clone, Copy)]
enum BoxFamily {
    Box,
    OptionBox,
}

#[derive(Default)]
struct RustInventoryVisitor {
    counts: RustCounts,
}

impl<'ast> Visit<'ast> for RustInventoryVisitor {
    fn visit_local(&mut self, local: &'ast syn::Local) {
        count_local_pat(&local.pat, &mut self.counts.types);
        visit::visit_local(self, local);
    }

    fn visit_signature(&mut self, signature: &'ast syn::Signature) {
        for input in &signature.inputs {
            if let syn::FnArg::Typed(input) = input {
                increment_type_position(
                    box_family(&input.ty),
                    &mut self.counts.types.param_box,
                    &mut self.counts.types.param_option_box,
                );
            }
        }
        if let syn::ReturnType::Type(_, ty) = &signature.output {
            increment_type_position(
                box_family(ty),
                &mut self.counts.types.return_box,
                &mut self.counts.types.return_option_box,
            );
        }
        visit::visit_signature(self, signature);
    }

    fn visit_field(&mut self, field: &'ast syn::Field) {
        increment_type_position(
            box_family(&field.ty),
            &mut self.counts.types.field_box,
            &mut self.counts.types.field_option_box,
        );
        visit::visit_field(self, field);
    }

    fn visit_expr_call(&mut self, call: &'ast syn::ExprCall) {
        if let syn::Expr::Path(function) = call.func.as_ref() {
            let mut segments = function.path.segments.iter().rev();
            let Some(last) = segments.next() else {
                return;
            };
            let associated_with_box = segments
                .next()
                .is_some_and(|segment| segment.ident == "Box");
            if last.ident == "malloc" {
                self.counts.malloc_calls += 1;
            } else if last.ident == "calloc" {
                self.counts.calloc_calls += 1;
            } else if last.ident == "realloc" {
                self.counts.realloc_calls += 1;
            } else if last.ident == "free" {
                self.counts.free_calls += 1;
            } else if last.ident == "drop" {
                self.counts.drop_calls += 1;
            } else if associated_with_box {
                if last.ident == "new" {
                    self.counts.box_new_calls += 1;
                } else if last.ident == "from_raw" {
                    self.counts.box_from_raw_calls += 1
                } else if last.ident == "into_raw" {
                    self.counts.box_into_raw_calls += 1
                }
            }
        }
        visit::visit_expr_call(self, call);
    }
}

fn count_local_pat(pat: &syn::Pat, counts: &mut TypePositionCounts) {
    match pat {
        syn::Pat::Type(typed) => {
            increment_type_position(
                box_family(&typed.ty),
                &mut counts.local_box,
                &mut counts.local_option_box,
            );
            count_local_pat(&typed.pat, counts);
        }
        syn::Pat::Paren(paren) => count_local_pat(&paren.pat, counts),
        syn::Pat::Reference(reference) => count_local_pat(&reference.pat, counts),
        syn::Pat::Slice(slice) => {
            for element in &slice.elems {
                count_local_pat(element, counts);
            }
        }
        syn::Pat::Struct(structure) => {
            for field in &structure.fields {
                count_local_pat(&field.pat, counts);
            }
        }
        syn::Pat::Tuple(tuple) => {
            for element in &tuple.elems {
                count_local_pat(element, counts);
            }
        }
        syn::Pat::TupleStruct(tuple) => {
            for element in &tuple.elems {
                count_local_pat(element, counts);
            }
        }
        _ => {}
    }
}

fn increment_type_position(family: Option<BoxFamily>, plain: &mut u64, optional: &mut u64) {
    match family {
        Some(BoxFamily::Box) => *plain += 1,
        Some(BoxFamily::OptionBox) => *optional += 1,
        None => {}
    }
}

fn box_family(ty: &syn::Type) -> Option<BoxFamily> {
    let ty = match ty {
        syn::Type::Group(group) => group.elem.as_ref(),
        syn::Type::Paren(paren) => paren.elem.as_ref(),
        _ => ty,
    };
    let syn::Type::Path(path) = ty else {
        return None;
    };
    let last = path.path.segments.last()?;
    if last.ident == "Box" {
        return Some(BoxFamily::Box);
    }
    if last.ident != "Option" {
        return None;
    }
    let syn::PathArguments::AngleBracketed(arguments) = &last.arguments else {
        return None;
    };
    let inner = arguments.args.iter().find_map(|argument| match argument {
        syn::GenericArgument::Type(ty) => Some(ty),
        _ => None,
    })?;
    matches!(box_family(inner), Some(BoxFamily::Box)).then_some(BoxFamily::OptionBox)
}

fn parse_json_document(name: &str, source: &str) -> Result<serde_json::Value, String> {
    serde_json::from_str(source).map_err(|error| format!("{name}: {error}"))
}

fn count_qualifier_scope(
    document: &str,
    root: &serde_json::Value,
    scope: &str,
    expected_labels: &[&str],
    counts: &mut BTreeMap<String, u64>,
    by_depth: &mut Vec<BTreeMap<String, u64>>,
    max_depth: &mut usize,
) -> Result<(), String> {
    let root = root
        .as_object()
        .ok_or_else(|| format!("{document}: root must be an object"))?;
    let owners = root
        .get(scope)
        .ok_or_else(|| format!("{document}: missing {scope}"))?
        .as_object()
        .ok_or_else(|| format!("{document}: {scope} must be an object"))?;
    for (owner, slots) in owners {
        let slots = slots
            .as_object()
            .ok_or_else(|| format!("{document}: {scope}.{owner} must be an object"))?;
        for (slot, labels) in slots {
            let labels = labels
                .as_array()
                .ok_or_else(|| format!("{document}: {scope}.{owner}.{slot} must be an array"))?;
            *max_depth = (*max_depth).max(labels.len());
            if by_depth.len() < labels.len() {
                by_depth.resize_with(labels.len(), BTreeMap::new);
            }
            for (depth, label) in labels.iter().enumerate() {
                let label = label.as_str().ok_or_else(|| {
                    format!("{document}: {scope}.{owner}.{slot}[{depth}] must be a string")
                })?;
                if !expected_labels.contains(&label) {
                    return Err(format!(
                        "{document}: unexpected label {label} at {scope}.{owner}.{slot}[{depth}]"
                    ));
                }
                *counts.entry(label.to_owned()).or_default() += 1;
                *by_depth[depth].entry(label.to_owned()).or_default() += 1;
            }
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn counts_only_declared_box_family_positions_and_real_calls() {
        let source = r#"
            extern "C" {
                fn malloc(size: usize) -> *mut u8;
                fn free(ptr: *mut u8);
            }

            // Box::new(99); free(ptr);
            struct Example {
                plain: Box<u8>,
                optional: core::option::Option<std::boxed::Box<u16>>,
                nested_but_not_a_position: Vec<Box<u32>>,
            }

            fn convert(
                plain: std::boxed::Box<u8>,
                optional: Option<Box<u16>>,
                raw: *mut u8,
            ) -> Option<Box<u32>> {
                let local_plain: Box<u8> = Box::new(1);
                let local_optional: Option<Box<u8>> = Some(Box::new(2));
                let nested_local: Vec<Box<u8>> = Vec::new();
                malloc(1);
                calloc(1, 2);
                realloc(raw, 3);
                free(raw);
                drop(local_plain);
                let _ = (local_optional, nested_local);
                None
            }
        "#;

        let counts = analyze_rust_source(source).unwrap();
        assert_eq!(
            counts.types,
            TypePositionCounts {
                local_box: 1,
                local_option_box: 1,
                param_box: 1,
                param_option_box: 1,
                return_option_box: 1,
                field_box: 1,
                field_option_box: 1,
                ..TypePositionCounts::default()
            }
        );
        assert_eq!(counts.box_new_calls, 2);
        assert_eq!(counts.malloc_calls, 1);
        assert_eq!(counts.calloc_calls, 1);
        assert_eq!(counts.realloc_calls, 1);
        assert_eq!(counts.free_calls, 1);
        assert_eq!(counts.drop_calls, 1);
    }

    #[test]
    fn preserves_native_json_labels_and_pointer_depths() {
        let ownership = r#"{
            "fn_data": {"crate::f": {"x": ["Owning", "Unknown"], "y": ["Transient"]}},
            "struct_data": {"crate::S": {"field": ["Owning"]}}
        }"#;
        let statistics = r#"{
            "num_unsafe_ptrs": 3,
            "num_non_arr_unsafe_ptrs": 2,
            "num_mut_unsafe_ptrs": 1,
            "num_non_arr_mut_unsafe_ptrs": 1,
            "num_unsafe_usages": 4,
            "num_non_arr_unsafe_usages": 3,
            "num_mut_unsafe_usages": 2,
            "num_non_arr_mut_unsafe_usages": 1,
            "num_owning_ptrs_detected": 2
        }"#;
        let mutability = r#"{
            "fn_data": {"crate::f": {"x": ["Mut", "Imm"]}},
            "struct_data": {"crate::S": {"field": ["Mut"]}}
        }"#;
        let fatness = r#"{
            "fn_data": {"crate::f": {"x": ["Ptr", "Arr"]}},
            "struct_data": {"crate::S": {"field": ["Ptr"]}}
        }"#;

        let claims = analyze_json_claims(ownership, statistics, mutability, fatness).unwrap();
        assert_eq!(claims.ownership_fn["Owning"], 1);
        assert_eq!(claims.ownership_fn["Unknown"], 1);
        assert_eq!(claims.ownership_fn["Transient"], 1);
        assert_eq!(claims.ownership_struct["Owning"], 1);
        assert_eq!(claims.ownership_fn_by_depth[0]["Owning"], 1);
        assert_eq!(claims.ownership_fn_by_depth[0]["Transient"], 1);
        assert_eq!(claims.ownership_fn_by_depth[1]["Unknown"], 1);
        assert_eq!(claims.ownership_struct_by_depth[0]["Owning"], 1);
        assert_eq!(claims.mutability_fn["Mut"], 1);
        assert_eq!(claims.mutability_fn["Imm"], 1);
        assert_eq!(claims.mutability_fn_by_depth[0]["Mut"], 1);
        assert_eq!(claims.mutability_fn_by_depth[1]["Imm"], 1);
        assert_eq!(claims.fatness_fn["Ptr"], 1);
        assert_eq!(claims.fatness_fn["Arr"], 1);
        assert_eq!(claims.fatness_fn_by_depth[0]["Ptr"], 1);
        assert_eq!(claims.fatness_fn_by_depth[1]["Arr"], 1);
        assert_eq!(claims.statistics["num_owning_ptrs_detected"], 2);
        assert_eq!(claims.max_depth, 2);
    }

    #[test]
    fn rejects_structurally_invalid_analysis_json() {
        let missing_scope = r#"{"fn_data": {}}"#;
        let statistics = r#"{
            "num_unsafe_ptrs": 3,
            "num_non_arr_unsafe_ptrs": 2,
            "num_mut_unsafe_ptrs": 1,
            "num_non_arr_mut_unsafe_ptrs": 1,
            "num_unsafe_usages": 4,
            "num_non_arr_unsafe_usages": 3,
            "num_mut_unsafe_usages": 2,
            "num_non_arr_mut_unsafe_usages": 1,
            "num_owning_ptrs_detected": 1
        }"#;
        let valid_qualifier = r#"{"fn_data": {}, "struct_data": {}}"#;

        let error =
            analyze_json_claims(missing_scope, statistics, valid_qualifier, valid_qualifier)
                .unwrap_err();
        let error = error.to_string();
        assert!(error.contains("ownership.json"));
        assert!(error.contains("struct_data"));

        let missing_statistic = statistics.replace(
            r#""num_owning_ptrs_detected": 1"#,
            r#""unexpected_counter": 1"#,
        );
        let error = analyze_json_claims(
            valid_qualifier,
            &missing_statistic,
            valid_qualifier,
            valid_qualifier,
        )
        .unwrap_err();
        let error = error.to_string();
        assert!(error.contains("statistics.json"));
        assert!(error.contains("num_owning_ptrs_detected"));
    }
}
