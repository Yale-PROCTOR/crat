//! Native robotfindskitten `message` literal-call regression witnesses.
use crate::{bo_rewriter as rewriter, bo_rewriter::decision::seam::SeamBlock};

fn check_literal(input: &str) {
    check_origin(input, true);
}

fn check_origin(input: &str, held: bool) {
    let source = ::utils::compilation::run_compiler_on_str(input, |tcx| {
        let capture = rewriter::ast_transform::capture_ast(tcx).expect("capture original AST");
        let (table, ctx) = rewriter::decide_table_with_ctx_config(
            tcx,
            Some((
                rewriter::A5Mode::PreciseReplay,
                Some(rewriter::WholeProgramAttestation::FrozenBenchmarkGraph),
            )),
        )
        .expect("native decisions");
        for (subject, decision) in &table.entries {
            println!("DECISION {} {decision:?}", subject.label);
        }
        println!("BLOCKED {:?}", table.seams.blocked);
        assert_eq!(
            table
                .seams
                .blocked
                .iter()
                .any(|row| row.block == SeamBlock::SharedToMut),
            held,
            "only immutable origins need a typed permission hold before AST emission"
        );
        let emission =
            rewriter::emit_files(tcx, &table, &Default::default(), &ctx.retained_c9_plans)
                .expect("native emission plan");
        let reverts = rewriter::ast_transform::revert_set_from_classes_and_atoms(
            &emission.plan.held_classes(),
            &Default::default(),
            &table,
        )
        .expect("planned held classes");
        rewriter::ast_transform::ast_emitted_files_from(
            tcx,
            &capture,
            &reverts,
            emission.plan.root_file.as_ref(),
            &table,
            Some(&emission.plan.terminal_call_plans),
        )
        .expect("native AST emission")
        .0
        .into_values()
        .next()
        .expect("one source")
    })
    .expect("input type checks");
    println!("EMITTED {source}");
    assert!(
        rewriter::verify::type_checks_str(&source),
        "raw fallback compiles: {source}"
    );
    if held {
        assert!(
            source.contains("message(p: *mut i8)"),
            "callee stays raw: {source}"
        );
        assert!(
            !source.contains("&mut *"),
            "no mutable reference from shared origin: {source}"
        );
    } else {
        assert!(
            source.contains("message(p: &mut i8)"),
            "mutable origin remains deliverable: {source}"
        );
    }
}

#[test]
fn wave6r_literal_bye_call_is_held_before_emission() {
    check_literal(
        r#"
        #![allow(dead_code, unused_unsafe)]
        unsafe extern "C" { fn mvprintw(y: i32, x: i32, format: *const i8, ...) -> i32; }
        unsafe fn message(p: *mut i8) {
            mvprintw(1, 0, b"%.*s\0" as *const u8 as *const i8, 80i32, p);
        }
        pub unsafe fn goodbye() { message(b"Bye!\0" as *const u8 as *const i8 as *mut i8); }
    "#,
    );
}

#[test]
fn wave6r_literal_invalid_input_call_is_held_before_emission() {
    check_literal(
        r#"
        #![allow(dead_code, unused_unsafe)]
        unsafe extern "C" { fn mvprintw(y: i32, x: i32, format: *const i8, ...) -> i32; }
        unsafe fn message(p: *mut i8) {
            mvprintw(1, 0, b"%.*s\0" as *const u8 as *const i8, 80i32, p);
        }
        pub unsafe fn process_input() { message(b"Invalid input: Use direction keys or Esc.\0" as *const u8 as *const i8 as *mut i8); }
    "#,
    );
}

#[test]
fn wave6r_literal_shared_reference_call_is_held_before_emission() {
    check_literal(
        r#"
        #![allow(dead_code, unused_unsafe)]
        unsafe extern "C" { fn mvprintw(y: i32, x: i32, format: *const i8, ...) -> i32; }
        unsafe fn message(p: *mut i8) {
            mvprintw(1, 0, b"%.*s\0" as *const u8 as *const i8, 1i32, p);
        }
        unsafe extern "C" { static SHARED: &'static i8; }
        pub unsafe fn process_input() { message(SHARED as *const i8 as *mut i8); }
    "#,
    );
}

#[test]
fn wave6r_literal_mutable_address_stays_deliverable() {
    check_origin(
        r#"
        #![allow(dead_code, unused_unsafe)]
        unsafe extern "C" { fn mvprintw(y: i32, x: i32, format: *const i8, ...) -> i32; }
        unsafe fn message(p: *mut i8) {
            mvprintw(1, 0, b"%.*s\0" as *const u8 as *const i8, 1i32, p);
        }
        pub unsafe fn process_input() {
            let mut value: i8 = 0;
            message(&mut value);
        }
    "#,
        false,
    );
}

#[test]
fn wave6r_literal_unknown_const_raw_origin_stays_deliverable() {
    check_origin(
        r#"
        #![allow(dead_code, unused_unsafe)]
        unsafe extern "C" {
            static RAW: *const i8;
            fn mvprintw(y: i32, x: i32, format: *const i8, ...) -> i32;
        }
        unsafe fn message(p: *mut i8) {
            mvprintw(1, 0, b"%.*s\0" as *const u8 as *const i8, 1i32, p);
        }
        pub unsafe fn process_input() { message(RAW as *mut i8); }
    "#,
        false,
    );
}
