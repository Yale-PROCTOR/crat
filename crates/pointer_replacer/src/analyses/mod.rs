#[cfg(test)]
#[allow(non_snake_case)]
pub mod B02_tests;
pub mod borrow;
mod encoding;
mod lattice;
mod liveness;
mod mir;
pub mod mir_variable_grouping;
pub mod offset_sign;
pub(crate) mod output_params;
pub mod ownership;
pub mod type_qualifier;
