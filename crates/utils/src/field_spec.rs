//! shared record types for struct-param field specialization: the pointer
//! pass emits these instead of ABI wrappers, and a later pass (the interface
//! fixer) consumes them to synthesize the actual C-facing wrappers.

#[derive(Clone, Debug, serde::Serialize, serde::Deserialize)]
pub struct FieldSpecParam {
    pub index: usize,
    pub struct_name: String,
    pub field: String,
    pub mutbl: String, // "const" | "mut"
}

#[derive(Clone, Debug, serde::Serialize, serde::Deserialize)]
pub struct FieldSpecEntry {
    pub internal: String,
    pub module: String,
    pub attr: FieldSpecAttr,
    pub params: Vec<FieldSpecParam>,
}

#[derive(Clone, Debug, serde::Serialize, serde::Deserialize)]
pub enum FieldSpecAttr {
    NoMangle,
    ExportName(String),
}

pub type FieldSpecMap = std::collections::BTreeMap<String, FieldSpecEntry>;
