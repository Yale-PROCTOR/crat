//! R376 native witnesses: actual model grants, compiled delivered types and
//! identity-matched frees. The unsafe input fixtures are never executed.

use super::decision::Decision;

fn fixture(element: &str, callee_body: &str, caller_body: &str) -> String {
    format!(
        r#"
        #![allow(dead_code,unused_unsafe,unused_mut,non_camel_case_types)]
        mod libc {{ pub use core::ffi::c_ulong; }}
        type uint16_t=u16;
        extern "C" {{
            fn calloc(count:libc::c_ulong,size:libc::c_ulong)->*mut core::ffi::c_void;
            fn free(ptr:*mut core::ffi::c_void);
        }}
        unsafe fn edt_with_payload(input:*mut {element},output:*mut {element},height:i32) {{ {callee_body} }}
        pub unsafe fn transform_to_coordfield(width:i32,height:i32)->{element} {{ {caller_body} }}
        "#,
    )
}

fn dimensions_fixture(extra: &str) -> String {
    fixture(
        "f32",
        "*output=*input+height as f32;",
        &format!(
            r#"
            let size=width*height;
            let mut pl1=calloc(size as libc::c_ulong,core::mem::size_of::<f32>() as libc::c_ulong) as *mut f32;
            let mut pl2=calloc(((height+1)*(width+1)) as libc::c_ulong,core::mem::size_of::<f32>() as libc::c_ulong) as *mut f32;
            *pl1=3.0;
            {extra}
            edt_with_payload(pl1,pl2,height);
            let result=*pl1+*pl2;
            let before_free=result;
            free(pl1 as *mut core::ffi::c_void);
            free(pl2 as *mut core::ffi::c_void);
            let after_free=before_free;
            after_free
            "#,
        ),
    )
}

fn require_native_model(input: &str, held_source_use: bool) {
    ::utils::compilation::run_compiler_on_str(input, |tcx| {
        let (table, ctx) = super::decide_table_with_ctx_config(
            tcx,
            Some((
                super::A5Mode::PreciseReplay,
                Some(super::WholeProgramAttestation::FrozenBenchmarkGraph),
            )),
        )
        .expect("actual CP2 fixture model");
        let mut checked = 0;
        for (subject, decision) in &table.entries {
            let name = subject.param_name.as_deref();
            if !matches!(name, Some("pl1" | "pl2")) || (held_source_use && name != Some("pl1")) {
                continue;
            }
            let slot = ctx.slots.fn_local_slots[&subject.fn_did]
                .slot_for_local_depth(subject.local, 0)
                .unwrap();
            let kind = ctx.model.get(&super::SlotRef::Local(subject.fn_did, slot));
            assert_eq!(
                kind,
                Some(&super::SlotKind::Owning),
                "real native grant for {}",
                subject.label
            );
            let owner = tcx.def_path_str(subject.fn_did.to_def_id());
            let key = subject.identity_key(&owner);
            let rows: Vec<_> = ctx
                .raw_boundary_artifacts
                .ownership_native
                .lines()
                .skip(1)
                .map(|line| line.split('\t').collect::<Vec<_>>())
                .filter(|row| row[0] == key)
                .collect();
            assert_eq!(rows.len(), 1, "one exact native subject identity");
            println!(
                "R376_NATIVE {} {kind:?} {decision:?} audit={:?}",
                subject.label, rows[0]
            );
            if held_source_use {
                assert!(matches!(decision, Decision::Degraded(_)));
                assert_eq!(rows[0][8], "held");
                assert_eq!(rows[0][9], "Source::UnsupportedOwnerUse");
            } else {
                assert!(
                    matches!(decision, Decision::Box(_)),
                    "R376 native admission for {}: {decision:?}",
                    subject.label
                );
                assert_eq!(rows[0][8], "selected");
            }
            checked += 1;
        }
        assert_eq!(checked, if held_source_use { 1 } else { 2 });
    })
    .expect("CP2 native input compiles");
}

fn require_emitted(input: &str, element: &str) -> String {
    require_native_model(input, false);
    let outcome = super::rewrite_core_injected(
        ::utils::compilation::str_to_input(input),
        None,
        super::MAX_REVERT_ROUNDS,
        &|_| {},
        false,
        false,
        false,
        Some((
            super::A5Mode::PreciseReplay,
            Some(super::WholeProgramAttestation::FrozenBenchmarkGraph),
        )),
    );
    let super::RewriteOutcome::Emitted {
        source,
        reverted_count,
        unplaceable,
        ..
    } = outcome
    else {
        panic!("CP2 native emission refused: {outcome:?}")
    };
    println!("R376_EMITTED_BEGIN\n{source}\nR376_EMITTED_END");
    assert_eq!(reverted_count, 0);
    assert!(unplaceable.is_empty());
    assert!(super::verify::type_checks_str(&source));
    let before = source
        .find("let before_free=")
        .expect("pre-free source marker");
    let after = source
        .find("let after_free=")
        .expect("post-free source marker");
    for name in ["pl1", "pl2"] {
        let spelling = format!("::std::mem::drop({name})");
        assert_eq!(
            source.matches(&spelling).count(),
            1,
            "one source occurrence per exact C free"
        );
        let at = source.find(&spelling).unwrap();
        assert!(
            before < at && at < after,
            "C free timing stays between its source markers"
        );
        assert!(!source.contains(&format!("free({name} as")));
    }
    ::utils::compilation::run_compiler_on_str(&source, |tcx| {
        let program = super::collect_program(tcx);
        let caller = *program
            .functions
            .iter()
            .find(|id| tcx.def_path_str(id.to_def_id()) == "transform_to_coordfield")
            .unwrap();
        let body = tcx.mir_drops_elaborated_and_const_checked(caller).borrow();
        for name in ["pl1", "pl2"] {
            let roots: Vec<_> = body
                .var_debug_info
                .iter()
                .filter(|info| info.name.as_str() == name)
                .filter_map(|info| match info.value {
                    rustc_middle::mir::VarDebugInfoContents::Place(place) => Some(place),
                    _ => None,
                })
                .collect();
            assert_eq!(roots.len(), 1, "unique compiled owner identity");
            let ty = roots[0].ty(&body.local_decls, tcx).ty;
            let rustc_middle::ty::TyKind::Adt(def, args) = ty.kind() else {
                panic!("{name} is not a compiled Box: {ty}")
            };
            assert!(def.is_box(), "{name}: {ty}");
            let rustc_middle::ty::TyKind::Slice(item) = args.type_at(0).kind() else {
                panic!("{name} does not own a slice: {ty}")
            };
            assert_eq!(item.to_string(), element);
            println!(
                "R376_CUSTODY {name} local={} type={ty}",
                roots[0].local.as_u32()
            );
        }
    })
    .unwrap();
    let drops = super::verify::box_mir_drops_str(&source).unwrap();
    let policies: Vec<_> = ["pl1", "pl2"]
        .into_iter()
        .map(|name| super::verify::BoxMirDropPolicy {
            subject: format!("transform_to_coordfield::{name}"),
            function: "transform_to_coordfield".into(),
            local_name: Some(name.into()),
            overwrite_sites: Vec::new(),
            retained_sink: true,
            optional: false,
            implicit_scope_close: false,
        })
        .collect();
    let receipt = super::verify::reconcile_box_mir_drop_policies(&drops, &policies).unwrap();
    assert!(
        drops.iter().all(|drop| drop.cleanup),
        "no implicit normal-path close replaces a C free"
    );
    println!("R376_DROP_CUSTODY_BEGIN\n{receipt}R376_DROP_CUSTODY_END");
    source
}

#[test]
fn r376_c_ulong_dimensions_emit_native_boxed_slices() {
    // ff/dd/zz/ww contribute these dimension/count and typed-zero shapes;
    // pl1/pl2 retain the direct-use fragment whose complete native proof exists.
    let source = require_emitted(&dimensions_fixture(""), "f32");
    assert!(source.contains("size as libc::c_ulong"));
    assert!(source.contains("(height+1)*(width+1)"));
}

#[test]
fn r376_uint16_cast_target_emits_native_numeric_boxes() {
    let input = fixture(
        "uint16_t",
        "*output=*input;",
        r#"
        let mut pl1=calloc(width as libc::c_ulong,core::mem::size_of::<uint16_t>() as libc::c_ulong) as *mut uint16_t;
        let mut pl2=calloc(height as libc::c_ulong,core::mem::size_of::<uint16_t>() as libc::c_ulong) as *mut uint16_t;
        *pl1=3;
        edt_with_payload(pl1,pl2,height);
        let result=*pl2;
        let before_free=result;
        free(pl1 as *mut core::ffi::c_void);
        free(pl2 as *mut core::ffi::c_void);
        let after_free=before_free;
        after_free
    "#,
    );
    let source = require_emitted(&input, "u16");
    assert!(source.contains("::std::vec![0u16;"));
}

#[test]
fn r376_loop_local_offsets_keep_each_generation_at_its_c_frees() {
    let input = fixture(
        "f32",
        "*output=*input+height as f32;",
        r#"
        let mut result=0.0;
        let mut index=0;
        while index<width {
            let mut pl1=calloc(height as libc::c_ulong,core::mem::size_of::<f32>() as libc::c_ulong) as *mut f32;
            let mut pl2=calloc(height as libc::c_ulong,core::mem::size_of::<f32>() as libc::c_ulong) as *mut f32;
            *pl1.offset((height-1) as isize)=3.0;
            *pl1=*pl1.offset((height-1) as isize);
            edt_with_payload(pl1,pl2,height);
            *pl2.offset((height-1) as isize)=*pl2;
            result+=*pl2.offset((height-1) as isize);
            let before_free=result;
            free(pl1 as *mut core::ffi::c_void);
            free(pl2 as *mut core::ffi::c_void);
            let after_free=before_free;
            result=after_free;
            index+=1;
        }
        result
    "#,
    );
    let source = require_emitted(&input, "f32");
    assert!(!source.contains("pl1.offset("));
    assert!(!source.contains("pl2.offset("));
    assert!(source.contains("while index<width"));
}

#[test]
fn r376_distinct_cursor_alias_stays_an_exact_native_source_hold() {
    let input = dimensions_fixture("let cursor=pl1.offset(1); *cursor=4.0;");
    require_native_model(&input, true);
}

#[test]
fn r376_effectful_scalar_lend_argument_stays_an_exact_source_hold() {
    let input = dimensions_fixture("")
        .replace(
            "type uint16_t=u16;",
            "type uint16_t=u16; fn height_next()->i32 { 1 }",
        )
        .replace(
            "edt_with_payload(pl1,pl2,height);",
            "edt_with_payload(pl1,pl2,height_next());",
        );
    require_native_model(&input, true);
}

#[test]
fn r376_effectful_constructor_count_runs_once_and_duplicate_fault_fails() {
    let input = r#"
        extern "C" { fn calloc(count:usize,size:usize)->*mut core::ffi::c_void; }
        fn next(calls:&mut usize)->usize { *calls+=1; 3 }
        unsafe fn seed(calls:&mut usize)->*mut f32 {
            calloc(next(calls),core::mem::size_of::<f32>()) as *mut f32
        }
    "#;
    let expression = ::utils::compilation::run_compiler_on_str(input, |tcx| {
        let owner = tcx
            .hir_body_owners()
            .find(|owner| tcx.item_name(owner.to_def_id()).as_str() == "seed")
            .unwrap();
        let rustc_hir::ExprKind::Block(block, _) = tcx.hir_body_owned_by(owner).value.kind else {
            panic!("seed block")
        };
        super::decision::ownership_fields_constructor::derive(
            tcx,
            owner,
            block.expr.unwrap(),
            tcx.types.f32,
        )
        .unwrap()
        .edit
        .replacement
    })
    .unwrap();
    assert_eq!(expression.matches("next(calls)").count(), 1);
    let fault = expression.replace("next(calls)", "{ let _ = next(calls); next(calls) }");
    for (label, count, succeeds) in [("once", expression, true), ("duplicated", fault, false)] {
        // These programs contain only safe Rust. Neither the input foreign
        // allocation nor any input raw-pointer dereference is executed.
        let source = format!(
            "fn next(calls:&mut usize)->usize {{ *calls+=1; 3 }} fn main() {{ let mut observed=0; let calls=&mut observed; let payload:Box<[f32]>={count}; assert_eq!(observed,1); assert_eq!(payload.as_ref(), &[0.0f32;3]); }}"
        );
        static NEXT: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
        let id = NEXT.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
        let dir = std::env::temp_dir().join(format!("crat-r376-count-{}-{id}", std::process::id()));
        std::fs::create_dir(&dir).unwrap();
        let input = dir.join("main.rs");
        let output = dir.join("program");
        std::fs::write(&input, &source).unwrap();
        let compiled = std::process::Command::new("rustc")
            .arg("--edition=2021")
            .arg(&input)
            .arg("-o")
            .arg(&output)
            .output()
            .unwrap();
        let run = compiled
            .status
            .success()
            .then(|| std::process::Command::new(&output).output().unwrap());
        std::fs::remove_dir_all(&dir).unwrap();
        assert!(
            compiled.status.success(),
            "{}",
            String::from_utf8_lossy(&compiled.stderr)
        );
        let run = run.unwrap();
        assert_eq!(
            run.status.success(),
            succeeds,
            "{label}: {}",
            String::from_utf8_lossy(&run.stderr)
        );
        println!(
            "R376_COUNT_{label} success={} {}",
            run.status.success(),
            String::from_utf8_lossy(&run.stderr)
        );
    }
}
