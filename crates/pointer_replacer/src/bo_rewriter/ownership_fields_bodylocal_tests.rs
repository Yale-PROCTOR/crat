//! R395 body-local fixtures. Raw inputs are compiled/analyzed, never executed.
use super::decision::{Decision, box_facts::BoxShape};

fn declarations() -> &'static str {
    r#"extern "C" { fn malloc(n:usize)->*mut core::ffi::c_void; fn calloc(n:usize,s:usize)->*mut core::ffi::c_void; fn free(p:*mut core::ffi::c_void); }"#
}

fn verify(input: &str, owner_name: &str, shape: BoxShape, transfer: bool) -> String {
    ::utils::compilation::run_compiler_on_str(input, |tcx| {
        let (table, ctx) = super::decide_table_with_ctx_config(
            tcx,
            Some((
                super::A5Mode::PreciseReplay,
                Some(super::WholeProgramAttestation::FrozenBenchmarkGraph),
            )),
        )
        .unwrap();
        let (subject, decision) = table
            .entries
            .iter()
            .find(|(s, _)| s.param_name.as_deref() == Some(owner_name))
            .unwrap();
        let slot = ctx.slots.fn_local_slots[&subject.fn_did]
            .slot_for_local_depth(subject.local, 0)
            .unwrap();
        assert_eq!(
            ctx.model.get(&super::SlotRef::Local(subject.fn_did, slot)),
            Some(&super::SlotKind::Owning),
            "actual model grant"
        );
        println!(
            "R395_NATIVE {} {decision:?}\n{}",
            subject.label, ctx.raw_boundary_artifacts.ownership_native
        );
        assert!(
            matches!(decision,Decision::Box(plan) if plan.shape==shape),
            "complete native Box expected: {decision:?}"
        );
    })
    .unwrap();
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
        panic!("{outcome:?}")
    };
    println!("R395_EMITTED_BEGIN {owner_name}\n{source}\nR395_EMITTED_END");
    assert_eq!(reverted_count, 0);
    assert!(unplaceable.is_empty());
    assert!(super::verify::type_checks_str(&source));
    if transfer {
        assert!(source.contains(&format!("::std::boxed::Box::into_raw({owner_name})")));
        assert!(!source.contains(&format!("::std::mem::drop({owner_name})")));
    } else {
        assert_eq!(
            source
                .matches(&format!("::std::mem::drop({owner_name})"))
                .count(),
            1
        );
    }
    ::utils::compilation::run_compiler_on_str(&source, |tcx| {
        let program = super::collect_program(tcx);
        let mut seen = 0;
        for f in program.functions {
            let body = tcx.mir_drops_elaborated_and_const_checked(f).borrow();
            for info in &body.var_debug_info {
                if info.name.as_str() != owner_name {
                    continue;
                }
                let rustc_middle::mir::VarDebugInfoContents::Place(p) = info.value else {
                    continue;
                };
                let ty = p.ty(&body.local_decls, tcx).ty;
                let rustc_middle::ty::TyKind::Adt(def, args) = ty.kind() else {
                    panic!("actual Box missing: {ty}")
                };
                assert!(def.is_box());
                assert_eq!(
                    matches!(args.type_at(0).kind(), rustc_middle::ty::TyKind::Slice(_)),
                    shape == BoxShape::Slice
                );
                println!("R395_CUSTODY {owner_name} {ty}");
                seen += 1;
            }
        }
        assert_eq!(seen, 1);
    })
    .unwrap();
    let drops = super::verify::box_mir_drops_str(&source).unwrap();
    assert!(
        drops
            .iter()
            .filter(|d| d.local_name.as_deref() == Some(owner_name))
            .all(|d| d.cleanup),
        "no implicit normal close replaces C free or follows transfer: {drops:?}"
    );
    println!("R395_DROP_CUSTODY {owner_name} transfer={transfer} observed={drops:?}");
    source
}

#[test]
fn r395_heman_tmp_malloc_local_without_owning_call() {
    let input = format!(
        "{} pub unsafe fn generate_gaussian_row()->i32 {{ let mut tmp=malloc(4*core::mem::size_of::<i32>()) as *mut i32; *tmp.offset(1)=7; let value=*tmp.offset(1); free(tmp as *mut core::ffi::c_void); value }}",
        declarations()
    );
    verify(&input, "tmp", BoxShape::Slice, false);
}

#[test]
fn r395_heman_gaussian_row_malloc_local_lends_and_keeps_owner() {
    let input = format!(
        "{} unsafe fn generate_gaussian_row(p:*mut i32) {{ *p=7; }} pub unsafe fn generate_gaussian_splat()->i32 {{ let mut gaussian_row=malloc(4*core::mem::size_of::<i32>()) as *mut i32; generate_gaussian_row(gaussian_row); let value=*gaussian_row; free(gaussian_row as *mut core::ffi::c_void); value }}",
        declarations()
    );
    let s = verify(&input, "gaussian_row", BoxShape::Slice, false);
    assert!(!s.contains("Box::into_raw"));
}

fn c_declarations() -> &'static str {
    r#"#![allow(non_camel_case_types)] pub mod libc { pub use core::ffi::c_int; pub use core::ffi::c_ulong; pub use core::ffi::c_float; pub use core::ffi::c_void; } extern "C" { fn malloc(n:libc::c_ulong)->*mut libc::c_void; fn free(p:*mut libc::c_void); }"#
}

#[test]
fn r395_heman_gaussian_splat_real_shape_wrapping_mul_count() {
    // The corpus shape of `generate_gaussian_splat::gaussian_row#3`: a
    // `wrapping_mul` byte count from a `c_int` parameter, a raw callee that
    // reads/writes through the formal and frees only its own allocation,
    // loop-carried `offset` reads, the C free at the end.
    let input = format!(
        r#"{}
pub unsafe extern "C" fn generate_gaussian_row(mut target: *mut libc::c_int, mut fwidth: libc::c_int) {{
    let mut nbytes = (fwidth as libc::c_ulong).wrapping_mul(::std::mem::size_of::<libc::c_int>() as libc::c_ulong) as libc::c_int;
    let mut tmp = malloc(nbytes as libc::c_ulong) as *mut libc::c_int;
    *tmp.offset(0 as libc::c_int as isize) = 1 as libc::c_int;
    *target.offset(0 as libc::c_int as isize) = *tmp.offset(0 as libc::c_int as isize);
    let mut col = 1 as libc::c_int;
    while col < fwidth {{
        *target.offset(col as isize) = 0 as libc::c_int;
        *tmp.offset(col as isize) = 0 as libc::c_int;
        col += 1;
    }}
    free(tmp as *mut libc::c_void);
}}
pub unsafe extern "C" fn generate_gaussian_splat(mut target: *mut libc::c_float, mut fwidth: libc::c_int) {{
    let mut gaussian_row = malloc((fwidth as libc::c_ulong).wrapping_mul(::std::mem::size_of::<libc::c_int>() as libc::c_ulong)) as *mut libc::c_int;
    generate_gaussian_row(gaussian_row, fwidth);
    let mut scale = 0.5f32;
    let mut j = 0 as libc::c_int;
    while j < fwidth {{
        let mut i = 0 as libc::c_int;
        while i < fwidth {{
            *target = (*gaussian_row.offset(i as isize) * *gaussian_row.offset(j as isize)) as libc::c_float * scale;
            target = target.offset(1);
            i += 1;
        }}
        j += 1;
    }}
    free(gaussian_row as *mut libc::c_void);
}}"#,
        c_declarations()
    );
    let s = verify(&input, "gaussian_row", BoxShape::Slice, false);
    assert!(!s.contains("Box::into_raw"));
    assert_eq!(
        s.matches("(fwidth as libc::c_ulong).wrapping_mul(::std::mem::size_of::<libc::c_int>() as libc::c_ulong)")
            .count(),
        2,
        "the complete byte expression is kept once at each allocation"
    );
}

#[test]
fn r395_heman_percentiles_real_shape_sizeof_first_wrapping_mul_count() {
    // `heman_ops_percentiles::vals#292`: sizeof-first operand order, an
    // index-written buffer read back in a loop, the C free at the end.
    let input = format!(
        r#"{}
pub unsafe extern "C" fn heman_ops_percentiles(mut src: *const libc::c_float, mut npixels: libc::c_int) -> libc::c_float {{
    let mut vals = malloc((::std::mem::size_of::<libc::c_float>() as libc::c_ulong).wrapping_mul(npixels as libc::c_ulong)) as *mut libc::c_float;
    let mut i = 0 as libc::c_int;
    while i < npixels {{
        *vals.offset(i as isize) = *src.offset(i as isize);
        i += 1;
    }}
    let mut acc = 0.0f32;
    let mut k = 0 as libc::c_int;
    while k < npixels {{
        acc += *vals.offset(k as isize);
        k += 1;
    }}
    free(vals as *mut libc::c_void);
    acc
}}"#,
        c_declarations()
    );
    let s = verify(&input, "vals", BoxShape::Slice, false);
    assert!(!s.contains("Box::into_raw"));
}

#[test]
fn r395_lodepng_shaped_local_transfers_to_freeing_callee() {
    // A body-local reduction of a C allocator/cleanup wrapper. The historical
    // lodepng Box cohort rows are parameters, not this synthetic local.
    let input = format!(
        "{} unsafe fn lodepng_free(p:*mut core::ffi::c_void) {{ free(p); }} pub unsafe fn prepare() {{ let mut buffer=malloc(core::mem::size_of::<u32>()) as *mut u32; *buffer=7; lodepng_free(buffer as *mut core::ffi::c_void); }}",
        declarations()
    );
    verify(&input, "buffer", BoxShape::Sized, true);
}

#[test]
fn r395_numeric_sized_local_lends_without_moving() {
    let input = format!(
        "{} unsafe fn touch(p:*mut u32) {{ *p=9; }} pub unsafe fn prepare()->u32 {{ let mut buffer=malloc(core::mem::size_of::<u32>()) as *mut u32; touch(buffer); let value=*buffer; free(buffer as *mut core::ffi::c_void); value }}",
        declarations()
    );
    let s = verify(&input, "buffer", BoxShape::Sized, false);
    assert!(!s.contains("Box::into_raw"));
}

#[test]
fn r395_scalar_returning_callee_keeps_caller_box() {
    let input = format!(
        "{} unsafe fn read(p:*mut u32)->u32 {{ *p }} pub unsafe fn prepare()->u32 {{ let mut buffer=calloc(2,core::mem::size_of::<u32>()) as *mut u32; *buffer=9; let value=read(buffer); free(buffer as *mut core::ffi::c_void); value }}",
        declarations()
    );
    let s = verify(&input, "buffer", BoxShape::Slice, false);
    assert!(!s.contains("Box::into_raw"));
}

#[test]
fn r395_transfer_site_has_no_later_root_use_or_second_free() {
    for suffix in [
        "let value=*buffer;",
        "free(buffer as *mut core::ffi::c_void);",
    ] {
        let input = format!(
            "{} unsafe fn release(p:*mut core::ffi::c_void) {{free(p);}} pub unsafe fn prepare() {{let mut buffer=calloc(2,core::mem::size_of::<u32>()) as *mut u32; release(buffer as *mut core::ffi::c_void); {suffix}}}",
            declarations()
        );
        ::utils::compilation::run_compiler_on_str(&input, |tcx| {
            let (table, ctx) = super::decide_table_with_ctx_config(
                tcx,
                Some((
                    super::A5Mode::PreciseReplay,
                    Some(super::WholeProgramAttestation::FrozenBenchmarkGraph),
                )),
            )
            .unwrap();
            let subject = &table
                .entries
                .iter()
                .find(|(s, _)| s.param_name.as_deref() == Some("buffer"))
                .unwrap()
                .0;
            let result = super::decision::ownership_fields_source::derive(
                &super::collect_program(tcx),
                subject,
                &ctx.constructions,
            );
            assert!(
                matches!(
                    result,
                    Err(
                        super::decision::ownership_fields_source::SourceHold::UnsupportedOwnerUse
                            | super::decision::ownership_fields_source::SourceHold::FreeIdentity
                    )
                ),
                "{suffix}: {result:?}"
            );
        })
        .unwrap();
    }
}

#[test]
fn r395_nonconsuming_void_call_preserves_target_pointer_cast() {
    let input = format!(
        "{} unsafe fn touch(p:*mut core::ffi::c_void) {{ let _=p; }} pub unsafe fn prepare()->u32 {{ let mut buffer=malloc(core::mem::size_of::<u32>()) as *mut u32; touch(buffer as *mut core::ffi::c_void); let value=*buffer; free(buffer as *mut core::ffi::c_void); value }}",
        declarations()
    );
    ::utils::compilation::run_compiler_on_str(&input, |tcx| {
        let (table, ctx) = super::decide_table_with_ctx_config(
            tcx,
            Some((
                super::A5Mode::PreciseReplay,
                Some(super::WholeProgramAttestation::FrozenBenchmarkGraph),
            )),
        )
        .unwrap();
        let (s, d) = table
            .entries
            .iter()
            .find(|(s, _)| s.param_name.as_deref() == Some("buffer"))
            .unwrap();
        let slot = ctx.slots.fn_local_slots[&s.fn_did]
            .slot_for_local_depth(s.local, 0)
            .unwrap();
        assert_eq!(
            ctx.model.get(&super::SlotRef::Local(s.fn_did, slot)),
            Some(&super::SlotKind::Raw)
        );
        assert!(
            matches!(d, Decision::Degraded(_)),
            "Raw model must remain held"
        );
    })
    .unwrap();
    // Mechanical bridge typing only; it does not substitute an Owning model.
    for shape in [BoxShape::Sized, BoxShape::Slice] {
        let view = super::decision::ownership_fields_native::raw_lend_argument(
            shape,
            "buffer",
            "u32",
            "*mut core::ffi::c_void",
        );
        let initializer = if shape == BoxShape::Sized {
            "Box::new(1u32)"
        } else {
            "vec![1u32;2].into_boxed_slice()"
        };
        let s = format!(
            "fn touch(_: *mut core::ffi::c_void) {{}} fn main() {{let mut buffer={initializer};touch({view});drop(buffer);}}"
        );
        assert!(super::verify::type_checks_str(&s));
    }
}

#[test]
fn r395_zero_capable_transfer_is_held() {
    let input = format!(
        "{} unsafe fn release(p:*mut core::ffi::c_void) {{ free(p); }} pub unsafe fn prepare(n:usize) {{ let mut buffer=calloc(n,core::mem::size_of::<u32>()) as *mut u32; release(buffer as *mut core::ffi::c_void); }}",
        declarations()
    );
    ::utils::compilation::run_compiler_on_str(&input, |tcx| {
        let (table, ctx) = super::decide_table_with_ctx_config(
            tcx,
            Some((
                super::A5Mode::PreciseReplay,
                Some(super::WholeProgramAttestation::FrozenBenchmarkGraph),
            )),
        )
        .unwrap();
        let (_, d) = table
            .entries
            .iter()
            .find(|(s, _)| s.param_name.as_deref() == Some("buffer"))
            .unwrap();
        assert!(matches!(d, Decision::Degraded(_)));
        assert!(
            ctx.raw_boundary_artifacts
                .ownership_native
                .contains("native-transfer-nonempty")
        );
    })
    .unwrap();
}

#[test]
fn r395_custom_global_allocator_is_not_a_c_free_contract() {
    let source = "#[global_allocator] static A:std::alloc::System=std::alloc::System; pub fn f(){}";
    ::utils::compilation::run_compiler_on_str(source, |tcx| {
        assert!(!super::decision::ownership_fields_native::c_free_allocator_compatible(tcx));
    })
    .unwrap();
}
