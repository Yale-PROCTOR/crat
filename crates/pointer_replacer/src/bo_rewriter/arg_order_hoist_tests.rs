//! **R631-12 (relay 130) — the argument-order hoist.** L01¹⁰'s arm (a) admits a
//! call whose argument list reads through the place a received reborrow
//! borrows (`insert_(tree, (*tree).root, …)`); the emission then owes the read
//! as a `let` above the reborrow. These witnesses run the hoist on an emitted
//! call directly: the analysis side is era-5c's.

use rustc_ast::mut_visit::MutVisitor;
use rustc_ast_pretty::pprust;
use rustc_hash::FxHashSet;

use super::{arg_order_hoist::HoistVisitor, ast_transform::Composition};

const PRELUDE: &str = "#![allow(dead_code, unused_unsafe, unused_mut, unused_variables)]\n\
pub struct Node { pub v: i32 }\n\
pub struct Tree { pub root: *mut Node, pub length: u32 }\n\
unsafe fn insert_(tree: &mut Tree, root: *mut Node, v: i32) -> i32 { tree.length += 1; 1 }\n\
unsafe fn insert_opt(tree: Option<&mut Tree>, root: *mut Node, v: i32) -> i32 { 1 }\n";

/// The span of the first call to `callee` in `krate`.
fn call_span(krate: &rustc_ast::Crate, callee: &str) -> (u32, u32) {
    struct Find<'a>(&'a str, Option<(u32, u32)>);
    impl<'ast> rustc_ast::visit::Visitor<'ast> for Find<'_> {
        fn visit_expr(&mut self, e: &'ast rustc_ast::Expr) {
            if self.1.is_none()
                && let rustc_ast::ExprKind::Call(f, _) = &e.kind
                && pprust::expr_to_string(f) == self.0
            {
                self.1 = Some((e.span.lo().0, e.span.hi().0));
            }
            rustc_ast::visit::walk_expr(self, e);
        }
    }
    let mut find = Find(callee, None);
    rustc_ast::visit::walk_crate(&mut find, krate);
    find.1.unwrap_or_else(|| panic!("no call to {callee}"))
}

/// The fixture after the hoist, with the calls to `callee` receipted when
/// `receipted`; also returns what the visitor applied and held.
fn hoisted(body: &str, callee: &str, receipted: bool) -> (String, usize, Vec<&'static str>) {
    rustc_span::create_default_session_globals_then(|| {
        let src = format!("{PRELUDE}{body}");
        let mut krate = ::utils::ast::parse_crate(src);
        let mut calls = FxHashSet::default();
        if receipted {
            calls.insert(call_span(&krate, callee));
        }
        let mut guard = Composition::default();
        let mut visitor = HoistVisitor::new(&calls, &mut guard);
        visitor.visit_crate(&mut krate);
        let (applied, held) = visitor.finish();
        let items = krate
            .items
            .iter()
            .map(|item| pprust::item_to_string(item))
            .collect::<Vec<_>>()
            .join("\n");
        (
            format!("#![allow(dead_code, unused_unsafe, unused_mut, unused_variables)]\n{items}"),
            applied,
            held,
        )
    })
}

fn compiles(text: &str) -> bool {
    super::verify::type_checks_str(text)
}

/// **Witness — a read through a glued reborrow is hoisted.** A nullable `tree`
/// received at a `&mut Tree` formal renders `tree.as_deref_mut().unwrap()`,
/// an explicit borrow, so the read of `(*tree…).root` in the same argument list
/// is E0499. The hoist reads it first.
#[test]
fn r631_12_a_read_through_a_glued_reborrow_is_hoisted() {
    let body = "pub unsafe fn tree_insert(mut tree: Option<&mut Tree>, v: i32) -> i32 {\n\
         \x20   if insert_(tree.as_deref_mut().unwrap(), (*tree.as_deref_mut().unwrap()).root, v) == 0 { return 0; }\n\
         \x20   1\n\
         }\n";
    let (base, _, _) = hoisted(body, "insert_", false);
    assert!(
        !compiles(&base),
        "RED: the unhoisted form is a borrow conflict\n{base}"
    );
    let (text, applied, held) = hoisted(body, "insert_", true);
    assert_eq!((applied, held.as_slice()), (1, &[][..]), "{text}");
    let flat = text.split_whitespace().collect::<Vec<_>>().join(" ");
    assert!(
        flat.contains("let __crat_hoist_")
            && flat.contains("= (*tree.as_deref_mut().unwrap()).root;"),
        "{text}"
    );
    assert!(compiles(&text), "the hoisted form type-checks\n{text}");
}

/// **Witness, the `Option` formal.** `tree.as_deref_mut()` at an optional
/// formal with a shared read of the same subject beside it is E0502.
#[test]
fn r631_12_a_read_beside_an_optional_reborrow_is_hoisted() {
    let body = "pub unsafe fn tree_insert(mut tree: Option<&mut Tree>, v: i32) -> i32 {\n\
         \x20   insert_opt(tree.as_deref_mut(), tree.as_deref().unwrap().root, v)\n\
         }\n";
    let (base, _, _) = hoisted(body, "insert_opt", false);
    assert!(!compiles(&base), "RED: E0502\n{base}");
    let (text, applied, _) = hoisted(body, "insert_opt", true);
    assert_eq!(applied, 1, "{text}");
    assert!(compiles(&text), "{text}");
}

/// **Control — the bare form.** A `&mut` local passed bare is a two-phase
/// implicit reborrow, which rustc accepts with the read beside it (quadtree's
/// `insert_(tree, (*tree).root, …)` as emitted). A receipted call is hoisted
/// all the same; the hoist keeps it well-typed.
#[test]
fn r631_12_the_bare_two_phase_form_compiles_either_way() {
    let body = "pub unsafe fn tree_insert(tree: &mut Tree, v: i32) -> i32 {\n\
         \x20   if insert_(tree, (*tree).root, v) == 0 { return 0; }\n\
         \x20   (*tree).length += 1;\n\
         \x20   1\n\
         }\n";
    let (base, _, _) = hoisted(body, "insert_", false);
    assert!(compiles(&base), "two-phase: {base}");
    let (text, applied, _) = hoisted(body, "insert_", true);
    assert_eq!(applied, 1, "{text}");
    assert!(compiles(&text), "{text}");
}

/// **Control — no receipt, no hoist.** The same conflicting call without an
/// arm-(a) receipt is left exactly as emitted (and reverts on its own).
#[test]
fn r631_12_a_call_without_a_receipt_is_unchanged() {
    let body = "pub unsafe fn tree_insert(mut tree: Option<&mut Tree>, v: i32) -> i32 {\n\
         \x20   insert_(tree.as_deref_mut().unwrap(), (*tree.as_deref_mut().unwrap()).root, v)\n\
         }\n";
    let (base, _, _) = hoisted(body, "insert_", false);
    let (text, applied, held) = hoisted(body, "insert_", false);
    assert_eq!((applied, held.len()), (0, 0));
    assert_eq!(text, base);
    assert!(!text.contains("__crat_hoist_"), "{text}");
}

/// **Control — a read not through the reborrowed place.** `reset_node_`'s
/// `quadtree_node_reset(node, (*tree).key_free)` shape: the read goes through
/// another local, so nothing is hoisted even with the receipt.
#[test]
fn r631_12_a_read_through_another_local_is_unchanged() {
    let body = "pub unsafe fn tree_insert(mut tree: Option<&mut Tree>, other: &mut Tree, v: i32) -> i32 {\n\
         \x20   insert_(tree.as_deref_mut().unwrap(), (*other).root, v)\n\
         }\n";
    let (base, _, _) = hoisted(body, "insert_", false);
    let (text, applied, held) = hoisted(body, "insert_", true);
    assert_eq!(applied, 0, "{text}");
    assert_eq!(held, ["no-read-through-a-received-reborrow"]);
    assert_eq!(text, base);
}

/// The wiring fixture: quadtree's shape with raw pointers, as the L01⁹ frame
/// decides it; the caller's parameter is `t`, the callee's `tree`.
const WIRING: &str = "#![allow(dead_code, unused_unsafe, unused_mut, unused_variables)]\n\
    pub struct Node { pub v: i32 }\n\
    pub struct Tree { pub root: *mut Node, pub length: u32 }\n\
    unsafe fn insert_(tree: *mut Tree, root: *mut Node, v: i32) -> i32 { (*tree).length += 1; (*root).v = v; 1 }\n\
    pub unsafe fn tree_insert(t: *mut Tree, v: i32) -> i32 {\n\
    \x20   if insert_(t, (*t).root, v) == 0 { return 0; }\n\
    \x20   1\n\
    }\n";

/// The emitted source and revert count of `WIRING` with the receipt for its
/// call to `insert_` injected; `as_ref` also decides `t` and `tree` `&mut`
/// (what L01¹⁰'s lend gives them).
fn wired(name: &str, as_ref: bool) -> (String, usize, u32) {
    let call = "insert_(t, (*t).root, v)";
    let lo = WIRING.find(call).expect("the call") as u32;
    let key = (lo, lo + call.len() as u32);
    let dir = std::env::temp_dir().join(format!("crat-r631-12-{name}-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let root = dir.join("lib.rs");
    std::fs::write(&root, WIRING).unwrap();
    let outcome = super::rewrite_m1_path_a5_injected(
        &root,
        super::A5Mode::PreciseReplay,
        Some(super::WholeProgramAttestation::FrozenBenchmarkGraph),
        &|table| {
            let (caller, local) = table
                .entries
                .iter()
                .find(|(subject, _)| subject.param_name.as_deref() == Some("t"))
                .map(|(subject, _)| (subject.fn_did, subject.local))
                .expect("tree_insert's parameter");
            table.arg_order_hoists.insert((key, caller, local));
            if as_ref {
                for (subject, decision) in &mut table.entries {
                    if matches!(subject.param_name.as_deref(), Some("t" | "tree")) {
                        *decision = super::decision::Decision::Ref { mutable: true };
                    }
                }
            }
        },
    );
    std::fs::remove_dir_all(dir).unwrap();
    match outcome {
        super::RewriteOutcome::Emitted {
            source,
            reverted_count,
            ..
        } => (source, reverted_count, lo),
        super::RewriteOutcome::Degraded { reason, .. } => panic!("degraded: {reason}"),
    }
}

/// **Wiring — a receipt in the table reaches the emission.** The analysis side
/// keys each arm-(a) application by the call's span (the MIR terminator's,
/// which is the call expression's), its caller and the received local; with
/// `t` emitted `&mut Tree`, the call is hoisted and the function kept.
#[test]
fn r631_12_a_table_receipt_hoists_the_emitted_call() {
    let (source, reverted, lo) = wired("ref", true);
    let flat = source.split_whitespace().collect::<Vec<_>>().join(" ");
    assert!(flat.contains("t: &mut Tree"), "{source}");
    assert!(
        flat.contains(&format!("let __crat_hoist_{lo}_1 = (*t).root;"))
            && flat.contains(&format!("insert_(t, __crat_hoist_{lo}_1, v)")),
        "{source}"
    );
    assert_eq!(reverted, 0, "{source}");
}

/// **Wiring control — a raw received subject is not hoisted.** At the L01⁹
/// frame `t` stays raw: it borrows nothing, so the receipt leaves the call as
/// written (and a revert-all round stays byte-identical to the input).
#[test]
fn r631_12_a_raw_received_subject_is_not_hoisted() {
    let (source, _, _) = wired("raw", false);
    assert!(!source.contains("__crat_hoist_"), "{source}");
    let flat = source.split_whitespace().collect::<Vec<_>>().join(" ");
    assert!(flat.contains("insert_(t, (*t).root, v)"), "{source}");
}
