//! **S3.2′-3 task 0 — the USE-CLASS CENSUS.**
//!
//! One question, asked before any mechanism exists: of a subject's uses, how
//! many have an image the Option wrapper can write, and how many do not?
//!
//! # Measurement only, and structurally so
//!
//! Nothing in `decide_one` reads this module, and it computes no verdict. In
//! particular it does **not** evaluate the split-back criterion — that is
//! pre-registered in the micro-plan (§9) and applied outside, on the numbers
//! this emits. An instrument that scored its own criterion would be the
//! circular shape the box-candidate split already cost us once.
//!
//! # The classes, fixed before the measurement
//!
//! In scope — each with a ratified image, from g02 (parameter idiom) or g05
//! (local idiom, where `unwrap()` would move the value out):
//!
//! | class | image |
//! |---|---|
//! | `null-test` | `p.is_none()` |
//! | `deref-read` | `*p.unwrap()` / `**p.as_ref().unwrap()` |
//! | `deref-write` | `*p.unwrap() = e` / `**p.as_mut().unwrap() = e` |
//! | `field-deref` | `p.unwrap().f` / `p.as_ref().unwrap().f` |
//!
//! Out of scope, each attributed rather than lumped: `call-arg`, `return`,
//! `cast`, `assign-target`, `assign-source`, `addr-of`, `raw-op-other`,
//! `binary-cmp`, `index`, `other`.
//!
//! # Reach, stated rather than discovered
//!
//! The classifier reads the **parent chain** of each path expression that
//! resolves to the subject's binding. Two limits ride with that and are
//! recorded here rather than in a reader's head:
//!
//! - `field-deref` does not distinguish read from write. Both take the same
//!   wrapper position, so the distinction would not change the class.
//! - `return` covers `ExprKind::Ret` **and** a block's tail expression. A tail
//!   expression is not necessarily the function's return value, so this
//!   over-counts `return` slightly — in the conservative direction, since every
//!   member of the class is out of scope either way.

use rustc_hash::FxHashMap;
use rustc_hir::{
    Expr, ExprKind, HirId, Node, QPath, UnOp,
    def::Res,
    def_id::LocalDefId,
    intravisit::{self, Visitor},
};
use rustc_middle::ty::TyCtxt;

/// The census columns, in the order they are emitted. In-scope classes first.
pub(crate) const CLASSES: &[&str] = &[
    "null-test",
    "deref-read",
    "deref-write",
    "field-deref",
    "call-arg",
    "return",
    "cast",
    "assign-target",
    "assign-source",
    "addr-of",
    "raw-op-other",
    "binary-cmp",
    "index",
    "other",
];

/// Raw-pointer methods, minus `is_null` — which has its own class because it is
/// the one raw-only method the wrapper *does* rewrite.
const RAW_OPS: &[&str] = &[
    "offset",
    "wrapping_offset",
    "add",
    "sub",
    "wrapping_add",
    "wrapping_sub",
    "offset_from",
    "read",
    "write",
    "read_volatile",
    "write_volatile",
    "copy_to",
    "copy_from",
    "as_ref",
    "as_mut",
];

/// Per-subject counts, indexed parallel to [`CLASSES`].
pub(crate) type Counts = Vec<u32>;

/// Every use of every binding in `functions`, classified.
///
/// Keyed by `(fn_did, binding_hir_id)` — the subject key the collector and the
/// emitability facts both use, so the join needs no translation.
pub(crate) fn collect(
    tcx: TyCtxt<'_>,
    functions: &[LocalDefId],
) -> FxHashMap<(LocalDefId, HirId), Counts> {
    struct V<'a, 'tcx> {
        tcx: TyCtxt<'tcx>,
        fn_did: LocalDefId,
        out: &'a mut FxHashMap<(LocalDefId, HirId), Counts>,
    }
    impl<'tcx> Visitor<'tcx> for V<'_, 'tcx> {
        fn visit_expr(&mut self, expr: &'tcx Expr<'tcx>) {
            if let ExprKind::Path(QPath::Resolved(_, path)) = &expr.kind
                && let Res::Local(hir_id) = path.res
            {
                let class = classify(self.tcx, expr);
                let idx = CLASSES
                    .iter()
                    .position(|c| *c == class)
                    .expect("classify returns a registered class");
                let entry = self
                    .out
                    .entry((self.fn_did, hir_id))
                    .or_insert_with(|| vec![0; CLASSES.len()]);
                entry[idx] += 1;
            }
            intravisit::walk_expr(self, expr);
        }
    }

    let mut out = FxHashMap::default();
    for &fn_did in functions {
        let Some(body_id) = tcx.hir_node_by_def_id(fn_did).body_id() else {
            continue;
        };
        let mut v = V {
            tcx,
            fn_did,
            out: &mut out,
        };
        v.visit_body(tcx.hir_body(body_id));
    }
    out
}

/// One use's class, from its parent node.
fn classify(tcx: TyCtxt<'_>, use_expr: &Expr<'_>) -> &'static str {
    let parent = tcx.parent_hir_node(use_expr.hir_id);
    let Node::Expr(p) = parent else {
        return match parent {
            // `let q = p;` — the subject flows into another binding.
            Node::LetStmt(_) => "assign-source",
            // A block's tail expression. See the module doc on over-counting.
            Node::Block(b) if b.expr.is_some_and(|e| e.hir_id == use_expr.hir_id) => "return",
            _ => "other",
        };
    };
    match &p.kind {
        ExprKind::MethodCall(seg, receiver, args, _) => {
            if receiver.hir_id == use_expr.hir_id {
                let name = seg.ident.name.to_string();
                if name == "is_null" {
                    "null-test"
                } else if RAW_OPS.contains(&name.as_str()) {
                    "raw-op-other"
                } else {
                    "other"
                }
            } else if args.iter().any(|a| a.hir_id == use_expr.hir_id) {
                "call-arg"
            } else {
                "other"
            }
        }
        ExprKind::Call(_, args) => {
            if args.iter().any(|a| a.hir_id == use_expr.hir_id) {
                "call-arg"
            } else {
                "other"
            }
        }
        ExprKind::Unary(UnOp::Deref, _) => classify_deref(tcx, p),
        ExprKind::Cast(..) => "cast",
        ExprKind::AddrOf(..) => "addr-of",
        ExprKind::Assign(lhs, ..) => {
            if lhs.hir_id == use_expr.hir_id {
                "assign-target"
            } else {
                "assign-source"
            }
        }
        ExprKind::AssignOp(_, lhs, _) => {
            if lhs.hir_id == use_expr.hir_id {
                "assign-target"
            } else {
                "assign-source"
            }
        }
        ExprKind::Binary(..) => "binary-cmp",
        ExprKind::Index(base, ..) => {
            if base.hir_id == use_expr.hir_id {
                "index"
            } else {
                "other"
            }
        }
        ExprKind::Ret(_) => "return",
        _ => "other",
    }
}

#[cfg(test)]
mod tests {
    /// **The classifier's accept-set, pinned per class.**
    ///
    /// The split-back criterion counts subjects whose every use is in scope, so
    /// a single mis-classification moves the branch decision. This asserts the
    /// **exact** count vector for one subject per class — a positive control for
    /// every class the census can reach, not a spot check.
    ///
    /// `index` has **no control and cannot have one**: `p[i]` does not type-check
    /// on a raw pointer, and the census runs on the input program, where every
    /// subject is still raw. The class is kept because a zero measured against a
    /// live classifier is evidence, where a missing class is silence — and the
    /// sweep's corpus-wide `index == 0` is the confirmation.
    #[test]
    fn every_reachable_use_class_has_a_control() {
        use std::fs;

        const SRC: &str = r#"#![allow(dead_code, unused_unsafe, unused_mut, unused_assignments, unused_variables)]
#[repr(C)]
pub struct S { pub f: i32 }
pub unsafe fn c_null(p: *mut i32) -> bool { p.is_null() }
pub unsafe fn c_read(p: *mut i32) -> i32 { *p }
pub unsafe fn c_write(p: *mut i32) { *p = 1; }
pub unsafe fn c_field(p: *mut S) -> i32 { (*p).f }
pub unsafe fn c_callarg(p: *mut i32) -> i32 { c_read(p) }
pub unsafe fn c_ret(p: *mut i32) -> *mut i32 { p }
pub unsafe fn c_cast(p: *mut i32) -> *mut u8 { p as *mut u8 }
pub unsafe fn c_assign_target(mut p: *mut i32) { p = 0 as *mut i32; }
pub unsafe fn c_assign_source(p: *mut i32) { let q = p; }
pub unsafe fn c_addrof(p: *mut i32) { let r = &p; }
pub unsafe fn c_rawop(p: *mut i32) -> i32 { *p.offset(1) }
pub unsafe fn c_cmp(p: *mut i32, q: *mut i32) -> bool { p == q }
"#;

        let dir = std::env::temp_dir().join(format!("crat-use-census-{}", std::process::id()));
        fs::create_dir_all(&dir).expect("fixture dir");
        let root = dir.join("lib.rs");
        fs::write(&root, SRC).expect("fixture written");

        let tsv = ::utils::compilation::run_compiler_on_path(&root, |tcx| {
            crate::bo_rewriter::use_census_tsv(tcx).expect("census")
        })
        .expect("fixture compiles");
        let _ = fs::remove_dir_all(&dir);

        let mut rows: std::collections::BTreeMap<String, Vec<u32>> = Default::default();
        for line in tsv.lines().skip(1) {
            let f: Vec<&str> = line.split('\t').collect();
            // The subject is the FIRST parameter of each control function.
            if f[1] == "1" {
                rows.insert(
                    f[0].rsplit("::").next().expect("fn name").to_string(),
                    f[4..].iter().map(|v| v.parse().expect("count")).collect(),
                );
            }
        }

        // (function, class, expected count in that class) — everything else 0.
        let expected: &[(&str, &str)] = &[
            ("c_null", "null-test"),
            ("c_read", "deref-read"),
            ("c_write", "deref-write"),
            ("c_field", "field-deref"),
            ("c_callarg", "call-arg"),
            ("c_ret", "return"),
            ("c_cast", "cast"),
            ("c_assign_target", "assign-target"),
            ("c_assign_source", "assign-source"),
            ("c_addrof", "addr-of"),
            ("c_rawop", "raw-op-other"),
            ("c_cmp", "binary-cmp"),
        ];

        for (func, class) in expected {
            let got = rows
                .get(*func)
                .unwrap_or_else(|| panic!("{func} has no census row; rows: {:?}", rows.keys()));
            let want: Vec<u32> = super::CLASSES
                .iter()
                .map(|c| u32::from(c == class))
                .collect();
            assert_eq!(
                got, &want,
                "{func}: expected exactly one `{class}` use.\n  classes: {:?}\n  got:     {got:?}",
                super::CLASSES
            );
        }
    }
}

/// `*p`'s class, from what encloses the deref.
fn classify_deref(tcx: TyCtxt<'_>, deref: &Expr<'_>) -> &'static str {
    let Node::Expr(g) = tcx.parent_hir_node(deref.hir_id) else {
        return "deref-read";
    };
    match &g.kind {
        ExprKind::Assign(lhs, ..) if lhs.hir_id == deref.hir_id => "deref-write",
        ExprKind::AssignOp(_, lhs, _) if lhs.hir_id == deref.hir_id => "deref-write",
        ExprKind::Field(base, _) if base.hir_id == deref.hir_id => "field-deref",
        ExprKind::AddrOf(..) => "addr-of",
        _ => "deref-read",
    }
}
