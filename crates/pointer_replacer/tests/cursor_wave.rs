//! R244 cursor preparation: exercises new leaf modules without changing the
//! production registry. No analysis admission or delivered-yield claim.

#![feature(rustc_private)]

extern crate rustc_ast;
extern crate rustc_ast_pretty;
extern crate rustc_driver;
extern crate rustc_span;

#[path = "../src/bo_rewriter/decision/cursor.rs"]
mod cursor;

#[path = "cursor_wave/index.rs"]
mod index_witnesses;

#[path = "cursor_wave/carrier.rs"]
mod carrier_witnesses;

#[path = "../src/bo_rewriter/cursor_ast.rs"]
mod cursor_ast;

#[path = "cursor_wave/lowering.rs"]
mod lowering_witnesses;

#[path = "cursor_wave/transaction.rs"]
mod transaction_witnesses;
