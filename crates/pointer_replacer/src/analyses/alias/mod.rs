use steensgaard::{
    FieldBased, FieldInsensitive, InterProcedural, MergeDeallocArg, NopDeallocArg, Steensgaard,
};

use crate::utils::rustc::RustProgram;

pub mod constraint;
pub mod steensgaard;
// #[cfg(test)]
// mod test;

pub type TaintResult = Steensgaard<FieldBased, MergeDeallocArg, InterProcedural>;
pub type AliasResult = Steensgaard<FieldInsensitive, NopDeallocArg, InterProcedural>;
pub type IntraAliasResult = Steensgaard<FieldInsensitive, NopDeallocArg, InterProcedural>;

pub fn taint_results(rust_program: &RustProgram) -> TaintResult {
    Steensgaard::field_based(rust_program)
}

pub fn alias_results(rust_program: &RustProgram) -> AliasResult {
    Steensgaard::field_insensitive(rust_program)
}

pub fn intra_alias_results(rust_program: &RustProgram) -> IntraAliasResult {
    Steensgaard::field_insensitive(rust_program)
}

pub fn report_results(rust_program: &RustProgram) {
    Steensgaard::<FieldBased, MergeDeallocArg, InterProcedural>::field_based(rust_program)
        .print_results()
}
