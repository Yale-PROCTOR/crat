use steensgaard::{
    FieldBased, FieldInsensitive, InterProcedural, MergeDeallocArg, NopDeallocArg, Steensgaard,
};

use crate::utils::rustc::RustProgram;

pub mod constraint;
pub mod steensgaard;
// #[cfg(test)]
// mod test;

#[allow(unused)]
pub type TaintResult = Steensgaard<FieldBased, MergeDeallocArg, InterProcedural>;
pub type AliasResult = Steensgaard<FieldInsensitive, NopDeallocArg, InterProcedural>;
#[allow(unused)]
pub type IntraAliasResult = Steensgaard<FieldInsensitive, NopDeallocArg, InterProcedural>;

#[allow(unused)]
pub fn taint_results(rust_program: &RustProgram) -> TaintResult {
    Steensgaard::field_based(rust_program)
}

pub fn alias_results(rust_program: &RustProgram) -> AliasResult {
    Steensgaard::field_insensitive(rust_program)
}

#[allow(unused)]
pub fn intra_alias_results(rust_program: &RustProgram) -> IntraAliasResult {
    Steensgaard::field_insensitive(rust_program)
}

#[allow(unused)]
pub fn report_results(rust_program: &RustProgram) {
    Steensgaard::<FieldBased, MergeDeallocArg, InterProcedural>::field_based(rust_program)
        .print_results()
}
