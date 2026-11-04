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

/// The spans of the call to `callee` in `krate` (its callee path's and each
/// argument's), and of every `__crat_hoist_*` binding's initializer.
fn node_spans(krate: &rustc_ast::Crate, callee: &str) -> (Vec<(u32, u32)>, Vec<(u32, u32)>) {
    struct Find<'a>(&'a str, Vec<(u32, u32)>, Vec<(u32, u32)>);
    impl<'ast> rustc_ast::visit::Visitor<'ast> for Find<'_> {
        fn visit_expr(&mut self, e: &'ast rustc_ast::Expr) {
            if let rustc_ast::ExprKind::Call(f, args) = &e.kind
                && pprust::expr_to_string(f) == self.0
            {
                self.1.push((f.span.lo().0, f.span.hi().0));
                self.1
                    .extend(args.iter().map(|a| (a.span.lo().0, a.span.hi().0)));
            }
            rustc_ast::visit::walk_expr(self, e);
        }

        fn visit_local(&mut self, local: &'ast rustc_ast::Local) {
            if pprust::pat_to_string(&local.pat).starts_with("__crat_hoist_")
                && let Some(init) = local.kind.init()
            {
                self.2.push((init.span.lo().0, init.span.hi().0));
            }
            rustc_ast::visit::walk_local(self, local);
        }
    }
    let mut find = Find(callee, Vec::new(), Vec::new());
    rustc_ast::visit::walk_crate(&mut find, krate);
    (find.1, find.2)
}

/// **R650-4 — the hoist keeps the call's own nodes.** The passes after it
/// find nodes by span (`wave5r_helper_path::qualify` qualifies an imported
/// helper call by its callee's span; wave-6l's C10), so the hoist moves the
/// callee and the arguments into its block instead of re-parsing their text.
#[test]
fn r650_4_the_hoist_keeps_the_call_s_own_nodes() {
    let body = "pub unsafe fn tree_insert(mut tree: Option<&mut Tree>, v: i32) -> i32 {\n\
         \x20   insert_(tree.as_deref_mut().unwrap(), (*tree.as_deref_mut().unwrap()).root, v)\n\
         }\n";
    rustc_span::create_default_session_globals_then(|| {
        let mut krate = ::utils::ast::parse_crate(format!("{PRELUDE}{body}"));
        let (before, _) = node_spans(&krate, "insert_");
        let mut calls = FxHashSet::default();
        calls.insert(call_span(&krate, "insert_"));
        let mut guard = Composition::default();
        let mut visitor = HoistVisitor::new(&calls, &mut guard);
        visitor.visit_crate(&mut krate);
        assert_eq!(visitor.finish().0, 1);
        let (after, bound) = node_spans(&krate, "insert_");
        // The callee and the two arguments left in place keep their spans; the
        // read moves into the binding with its own.
        assert_eq!(
            (after[0], after[1], after[3]),
            (before[0], before[1], before[3])
        );
        assert_eq!(bound, [before[2]]);
    });
}

/// **R666-6 (wave-6l 063 §2) — a span already hoisted is skipped.** wave-6l's
/// bracket moves a CLONE of the initializer's call into its constructor's
/// hole, so the wrapper keeps the call's span and `NodeId`. The hoist rewrites
/// the inner call, then meets the wrapper under the same key: it must not try
/// it again, or the receipt counts once `applied` and once `held`.
#[test]
fn r666_6_a_wrapper_carrying_the_call_s_span_is_not_hoisted_again() {
    let body = "pub unsafe fn tree_insert(mut tree: Option<&mut Tree>, v: i32) -> i32 {\n\
         \x20   let r = insert_(tree.as_deref_mut().unwrap(), (*tree.as_deref_mut().unwrap()).root, v);\n\
         \x20   r\n\
         }\n";
    rustc_span::create_default_session_globals_then(|| {
        let mut krate = ::utils::ast::parse_crate(format!("{PRELUDE}{body}"));
        let key = call_span(&krate, "insert_");
        // The bracket's move: the call node becomes a wrapper around its clone.
        struct Wrap((u32, u32));
        impl MutVisitor for Wrap {
            fn visit_expr(&mut self, e: &mut rustc_ast::Expr) {
                rustc_ast::mut_visit::walk_expr(self, e);
                if (e.span.lo().0, e.span.hi().0) == self.0 {
                    let mut wrapper =
                        super::ast_transform::graft_expr("core::convert::identity(0)").unwrap();
                    if let rustc_ast::ExprKind::Call(_, args) = &mut wrapper.kind {
                        args[0] = rustc_ast::ptr::P(e.clone());
                    }
                    e.kind = wrapper.kind;
                }
            }
        }
        Wrap(key).visit_crate(&mut krate);
        let mut calls = FxHashSet::default();
        calls.insert(key);
        let mut guard = Composition::default();
        let mut visitor = HoistVisitor::new(&calls, &mut guard);
        visitor.visit_crate(&mut krate);
        assert_eq!(visitor.finish(), (1, Vec::<&str>::new()));
        let text = krate
            .items
            .iter()
            .map(|item| pprust::item_to_string(item))
            .collect::<Vec<_>>()
            .join(" ");
        let flat = text.split_whitespace().collect::<Vec<_>>().join(" ");
        assert!(
            flat.contains("core::convert::identity({ let __crat_hoist_"),
            "the wrapper stays outermost: {flat}"
        );
    });
}

/// **R697-2 — the hoist on any program's L01¹¹ entry**, for the count the
/// relay asks: the calls hoisted, the first verify's borrow conflicts and the
/// reverts, read from the full rewrite of `CRAT_R697_ROOT` (cache-only).
/// Records only; asserts nothing about the program.
#[test]
#[ignore = "R697-2: a program's L01¹¹ frame; run by hand with CRAT_R697_ROOT and the frame's env"]
fn r697_2_the_hoist_by_program_on_the_frame() {
    let root = std::path::PathBuf::from(
        std::env::var("CRAT_R697_ROOT").expect("CRAT_R697_ROOT: the program's substrate lib.rs"),
    );
    assert_eq!(
        std::env::var("CRAT_ERA5_EXECUTION_ROLE").as_deref(),
        Ok("cache-only"),
        "the frame is read from its accepted cache, never solved"
    );
    let config = super::EmissionRunConfig {
        analysis_budget: Default::default(),
        configured_exposure: super::decision::exposure::ConfiguredExposureInput::checked(
            "standing-raw-boundary-launch:Config::default.c_exposed_fns",
            Vec::new(),
            "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855",
        )
        .expect("the configured exposure row (explicit-empty for all twenty)"),
    };
    let rewrite = |census_once: bool| {
        super::rewrite_core_injected_with_config(
            ::utils::compilation::path_to_input(&root),
            Some(&root),
            super::MAX_REVERT_ROUNDS,
            &|_| {},
            false,
            census_once,
            false,
            None,
            &config,
        )
    };
    let capture = rewrite(true)
        .into_e1_capture()
        .expect("the one-iteration capture");
    let conflicts = capture
        .first_diags
        .iter()
        .filter(|d| {
            ["E0499", "E0502", "E0503", "E0505", "E0506"]
                .iter()
                .any(|code| d.code.as_deref() == Some(code))
        })
        .map(|d| format!("{}:{}\t{}", d.line, d.column, d.message))
        .collect::<Vec<_>>();
    let (emitted, reverted) = match rewrite(false) {
        super::RewriteOutcome::Emitted {
            source,
            reverted_count,
            ..
        } => (source, reverted_count),
        super::RewriteOutcome::Degraded { reason, .. } => {
            (format!("DEGRADED {reason}"), usize::MAX)
        }
    };
    let hoisted = emitted
        .lines()
        .filter(|line| line.contains("__crat_hoist_") && !line.trim_start().starts_with("let "))
        .map(str::trim)
        .collect::<Vec<_>>();
    let record = [
        format!(
            "source={} hoist_lets={} reverted={reverted} first_verify_borrow_conflicts={}",
            capture.solve_receipt.source,
            emitted.matches("let __crat_hoist_").count(),
            conflicts.len()
        ),
        format!("hoisted={hoisted:?}"),
        format!("conflicts={conflicts:?}"),
    ]
    .join("\n");
    if let Ok(out) = std::env::var("CRAT_R697_OUT") {
        std::fs::write(out, &record).unwrap();
    }
    eprintln!("{record}");
}
