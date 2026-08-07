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
    // **S3.2′-3 task 2 — the POSITION axis for pointer arithmetic.**
    //
    // Appended, never interleaved: the in-scope set is unchanged, so the
    // split-back criterion already scored (`clean = 49`) is invariant under this
    // extension — asserted by re-running the sweep and re-checking the number,
    // not argued.
    //
    // Every one of these read `raw-op-other` before. They exist because -2's
    // out-of-scope position census — self-advance, rebind, borrow-of-deref — is
    // the reslice docket, and a docket needs its members counted.
    "arith-deref-read",
    "arith-deref-write",
    "arith-field",
    "arith-borrow",
    "arith-self-advance",
    "arith-rebind",
    "arith-call-arg",
    "arith-cast",
    "arith-other",
];

/// Pointer arithmetic — the ops whose *position* the reslice decision turns on.
const ARITH_OPS: &[&str] = &[
    "offset",
    "wrapping_offset",
    "add",
    "sub",
    "wrapping_add",
    "wrapping_sub",
    "offset_from",
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
                } else if ARITH_OPS.contains(&name.as_str()) {
                    arith_position(tcx, p)
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


/// **Where an arithmetic result lands** — the reslice decision's other axis.
///
/// `call` is the `p.offset(e)` expression itself. -2 authorised exactly two of
/// these positions (`arith-deref-read`, `arith-deref-write`); the rest are the
/// scope-amendment docket, and `arith-self-advance` versus `arith-rebind` is the
/// distinction the reslice idiom turns on — `p = &p[k..]` against
/// `let q = &p[k..]`.
fn arith_position(tcx: TyCtxt<'_>, call: &Expr<'_>) -> &'static str {
    match tcx.parent_hir_node(call.hir_id) {
        Node::Expr(p) => match &p.kind {
            ExprKind::Unary(UnOp::Deref, _) => match tcx.parent_hir_node(p.hir_id) {
                Node::Expr(g) => match &g.kind {
                    ExprKind::Assign(lhs, ..) if lhs.hir_id == p.hir_id => "arith-deref-write",
                    ExprKind::AssignOp(_, lhs, _) if lhs.hir_id == p.hir_id => "arith-deref-write",
                    ExprKind::Field(base, _) if base.hir_id == p.hir_id => "arith-field",
                    ExprKind::AddrOf(..) => "arith-borrow",
                    _ => "arith-deref-read",
                },
                _ => "arith-deref-read",
            },
            // `p = p.offset(e)` advances the subject itself; `q = p.offset(e)`
            // binds a new one. Only the first needs the `&mut` reslice idiom.
            ExprKind::Assign(lhs, rhs, _) if rhs.hir_id == call.hir_id => {
                if same_binding(lhs, call) {
                    "arith-self-advance"
                } else {
                    "arith-rebind"
                }
            }
            ExprKind::AddrOf(..) => "arith-borrow",
            ExprKind::Cast(..) => "arith-cast",
            ExprKind::Call(_, args) if args.iter().any(|a| a.hir_id == call.hir_id) => {
                "arith-call-arg"
            }
            ExprKind::MethodCall(_, _, args, _) if args.iter().any(|a| a.hir_id == call.hir_id) => {
                "arith-call-arg"
            }
            _ => "arith-other",
        },
        Node::LetStmt(_) => "arith-rebind",
        _ => "arith-other",
    }
}

/// Does the assignment target name the same binding the arithmetic reads?
fn same_binding(lhs: &Expr<'_>, call: &Expr<'_>) -> bool {
    fn binding_of(e: &Expr<'_>) -> Option<HirId> {
        match &e.kind {
            ExprKind::Path(QPath::Resolved(_, path)) => match path.res {
                Res::Local(id) => Some(id),
                _ => None,
            },
            _ => None,
        }
    }
    let ExprKind::MethodCall(_, receiver, ..) = &call.kind else {
        return false;
    };
    match (binding_of(lhs), binding_of(receiver)) {
        (Some(a), Some(b)) => a == b,
        _ => false,
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
pub unsafe fn c_rawop(p: *mut i32) -> i32 { p.read() }
pub unsafe fn c_cmp(p: *mut i32, q: *mut i32) -> bool { p == q }
pub unsafe fn c_arith_read(p: *mut i32) -> i32 { *p.offset(1) }
pub unsafe fn c_arith_write(p: *mut i32) { *p.offset(1) = 3; }
pub unsafe fn c_arith_field(p: *mut S) -> i32 { (*p.offset(1)).f }
pub unsafe fn c_arith_borrow(p: *mut i32) { let r = &mut *p.offset(1); }
pub unsafe fn c_arith_self(mut p: *mut i32) { p = p.offset(1); }
pub unsafe fn c_arith_rebind(p: *mut i32) { let q = p.offset(1); }
pub unsafe fn c_arith_callarg(p: *mut i32) -> i32 { c_read(p.offset(1)) }
pub unsafe fn c_arith_cast(p: *mut i32) -> *mut u8 { p.offset(1) as *mut u8 }
pub unsafe fn c_arith_other(p: *mut i32) -> *mut i32 { p.offset(1) }
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
                    f[5..].iter().map(|v| v.parse().expect("count")).collect(),
                );
            }
        }

        // (function, the FULL expected class multiset) — everything else 0.
        let expected: &[(&str, &[(&str, u32)])] = &[
            ("c_null", &[("null-test", 1)]),
            ("c_read", &[("deref-read", 1)]),
            ("c_write", &[("deref-write", 1)]),
            ("c_field", &[("field-deref", 1)]),
            ("c_callarg", &[("call-arg", 1)]),
            ("c_ret", &[("return", 1)]),
            ("c_cast", &[("cast", 1)]),
            ("c_assign_target", &[("assign-target", 1)]),
            ("c_assign_source", &[("assign-source", 1)]),
            ("c_addrof", &[("addr-of", 1)]),
            ("c_rawop", &[("raw-op-other", 1)]),
            ("c_cmp", &[("binary-cmp", 1)]),
            // The position axis. `c_arith_self` carries TWO uses of the subject
            // — the assignment target and the arithmetic receiver — which is why
            // the expectation is a multiset and not a single class.
            ("c_arith_read", &[("arith-deref-read", 1)]),
            ("c_arith_write", &[("arith-deref-write", 1)]),
            ("c_arith_field", &[("arith-field", 1)]),
            ("c_arith_borrow", &[("arith-borrow", 1)]),
            ("c_arith_self", &[("assign-target", 1), ("arith-self-advance", 1)]),
            ("c_arith_rebind", &[("arith-rebind", 1)]),
            ("c_arith_callarg", &[("arith-call-arg", 1)]),
            ("c_arith_cast", &[("arith-cast", 1)]),
            ("c_arith_other", &[("arith-other", 1)]),
        ];

        for (func, classes) in expected {
            let got = rows
                .get(*func)
                .unwrap_or_else(|| panic!("{func} has no census row; rows: {:?}", rows.keys()));
            let want: Vec<u32> = super::CLASSES
                .iter()
                .map(|c| {
                    classes
                        .iter()
                        .find_map(|(k, n)| (k == c).then_some(*n))
                        .unwrap_or(0)
                })
                .collect();
            assert_eq!(
                got, &want,
                "{func}: expected {classes:?}.\n  classes: {:?}\n  got:     {got:?}",
                super::CLASSES
            );
        }
    }
}
