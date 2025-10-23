mod error_analysis;
mod file_analysis;
mod likely_lit;
mod mir_loc;
mod transformation;

pub use transformation::transform::{replace_io, run};

#[cfg(test)]
mod tests;
