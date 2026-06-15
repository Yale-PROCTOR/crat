//! Experimental unified borrow/ownership analysis.
//!
//! This module is intentionally self-contained while it is being built out. The
//! existing `borrow` and `ownership` analyses remain the production baseline.
#![allow(dead_code)]

mod domain;
pub mod slots;

#[allow(unused_imports)]
pub use domain::SlotKind;
