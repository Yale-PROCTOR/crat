//! R347-5 new-module instrument witnesses. No production registry change.
#![feature(rustc_private)]

extern crate rustc_driver;
extern crate rustc_hir;
extern crate rustc_middle;

#[path = "../src/bo_rewriter/decision/cursor/admission.rs"]
mod admission;

#[path = "cursor_admission/compiler.rs"]
mod compiler;
