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

/// **R697-2 — quadtree's L01¹¹ frame: the loader feeds the hoist.** The frame's
/// entry records three arm-(a) receipts (`quadtree_insert` bb7[15] twice,
/// `quadtree_free` bb2[6]); the model decided `insert_`'s `tree` a reference on
/// the premise that `insert_(tree, (*tree).root, point, key)` reads the root
/// before the lend. Without the loader the call emits as written, E0502, and
/// `insert_`'s class reverts (the frame census's 21 rows). Read through the
/// census's one-iteration instrument on the frame's own entry, with no solve.
///
/// Run by hand, never by the suite: `CRAT_R697_QUADTREE=<…/rs-crown-derived/quadtree/lib.rs>`
/// with the frame's env; `CRAT_R697_OUT` names a file for the rows the report
/// quotes.
#[test]
#[ignore = "R697-2: quadtree's L01¹¹ frame; run by hand with CRAT_R697_QUADTREE and the frame's env"]
fn r697_2_quadtree_insert_hoists_on_the_frame() {
    let root = std::path::PathBuf::from(
        std::env::var("CRAT_R697_QUADTREE")
            .expect("CRAT_R697_QUADTREE: quadtree's substrate lib.rs"),
    );
    assert_eq!(
        std::env::var("CRAT_ERA5_EXECUTION_ROLE").as_deref(),
        Ok("cache-only"),
        "the frame is read from its accepted cache, never solved"
    );
    // The census's configured exposure row for quadtree (explicit-empty).
    let config = super::EmissionRunConfig {
        configured_exposure: super::decision::exposure::ConfiguredExposureInput::checked(
            "standing-raw-boundary-launch:Config::default.c_exposed_fns",
            Vec::new(),
            "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855",
        )
        .expect("quadtree's configured exposure row"),
    };
    let capture = super::rewrite_core_injected_with_config(
        ::utils::compilation::path_to_input(&root),
        Some(&root),
        super::MAX_REVERT_ROUNDS,
        &|_| {},
        false,
        true,
        false,
        None,
        &config,
    )
    .into_e1_capture()
    .expect("the one-iteration capture");
    // The one-iteration capture stops at the first verify (its diagnostics
    // are the E0502 question); the emitted tree is the full rewrite's.
    let (emitted, rewrite_reverted) = match super::rewrite_core_injected_with_config(
        ::utils::compilation::path_to_input(&root),
        Some(&root),
        super::MAX_REVERT_ROUNDS,
        &|_| {},
        false,
        false,
        false,
        None,
        &config,
    ) {
        super::RewriteOutcome::Emitted {
            source,
            reverted_count,
            ..
        } => (source, reverted_count),
        super::RewriteOutcome::Degraded { reason, .. } => panic!("degraded: {reason}"),
    };
    let flat = emitted.split_whitespace().collect::<Vec<_>>().join(" ");
    let hoists = flat.matches("let __crat_hoist_").count();
    let e0502 = capture
        .first_diags
        .iter()
        .filter(|d| d.message.contains("E0502") || d.message.contains("also borrowed as immutable"))
        .map(|d| format!("{}:{}\t{}", d.line, d.column, d.message))
        .collect::<Vec<_>>();
    let reverts = capture
        .reverts
        .iter()
        .map(|r| {
            format!(
                "{}\t{}\t{}",
                r.function, r.attribution, r.diagnostic.message
            )
        })
        .collect::<Vec<_>>();
    let insert_call = flat
        .find("__crat_hoist_")
        .map(|at| flat[at.saturating_sub(120)..(at + 200).min(flat.len())].to_owned())
        .unwrap_or_default();
    let record = [
        format!(
            "source={} reverted={} novel_errors={}",
            capture.solve_receipt.source, capture.reverted_count, capture.novel_error_count
        ),
        format!("rewrite_reverted={rewrite_reverted}"),
        format!(
            "insert_lines={:?}",
            emitted
                .lines()
                .filter(|line| line.contains("insert_("))
                .map(str::trim)
                .collect::<Vec<_>>()
        ),
        format!("hoist_lets={hoists}"),
        format!("insert_call={insert_call}"),
        format!("e0502={e0502:?}"),
        format!("reverts={reverts:?}"),
    ]
    .join("\n");
    if let Ok(out) = std::env::var("CRAT_R697_OUT") {
        std::fs::write(out, &record).unwrap();
    }
    eprintln!("{record}");
    assert!(e0502.is_empty(), "{record}");
    assert!(
        !reverts
            .iter()
            .any(|r| r.starts_with("src::src::quadtree::quadtree_insert")
                || r.starts_with("src::src::quadtree::insert_")),
        "{record}"
    );
    assert!(flat.contains("insert_(tree, __crat_hoist_"), "{record}");
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
