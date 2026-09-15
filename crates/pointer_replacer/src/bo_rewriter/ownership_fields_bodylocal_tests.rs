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
            "R395_NATIVE {} {decision:?}\n{}\nR395_FAMILY {:?}",
            subject.label,
            ctx.raw_boundary_artifacts.ownership_native,
            ctx.raw_boundary_artifacts.additive_family_receipts
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
        degradations,
        first_diags,
        ..
    } = outcome
    else {
        panic!("{outcome:?}")
    };
    println!("R395_EMITTED_BEGIN {owner_name}\n{source}\nR395_EMITTED_END");
    println!(
        "R395_OUTCOME reverted={reverted_count} degradations={:?} first_diags={first_diags:?}",
        degradations
            .iter()
            .map(|d| (d.subject.clone(), d.reason.key(), d.reason.detail()))
            .collect::<Vec<_>>()
    );
    // R402-2(a): the custody instrument must read an explicit, fully spelled
    // owning type on the delivered declaration.
    let declarations =
        super::delivery_custody::inventory_source("fixture.rs", &source).expect("custody parse");
    let declaration = declarations
        .iter()
        .find(|d| d.binding == owner_name && d.parameter_index.is_none())
        .unwrap_or_else(|| panic!("declaration of {owner_name}: {declarations:?}"));
    assert!(
        declaration.type_is_fully_explicit,
        "{owner_name}: {:?}",
        declaration.explicit_type
    );
    assert!(
        matches!(
            declaration.effective_type_shape(),
            Some(super::delivery_custody::TypeShape::OwningBox { path, payload })
                if path == "std::boxed::Box"
                    && matches!(payload.as_ref(), super::delivery_custody::TypeShape::Slice { .. })
                        == (shape == BoxShape::Slice)
        ),
        "{owner_name}: {:?}",
        declaration.effective_type_shape()
    );
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

fn gaussian_fixture() -> String {
    format!(
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
    )
}

#[test]
fn r395_heman_gaussian_splat_real_shape_wrapping_mul_count() {
    // The corpus shape of `generate_gaussian_splat::gaussian_row#3`: a
    // `wrapping_mul` byte count from a `c_int` parameter, a raw callee that
    // reads/writes through the formal and frees only its own allocation,
    // loop-carried `offset` reads, the C free at the end.
    let input = gaussian_fixture();
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
fn r399_heman_gaussian_row_tmp_real_shape_narrowed_nbytes_local() {
    // `generate_gaussian_row::tmp#68`: the byte count is the `c_int` local
    // `nbytes`, initialised once from the `wrapping_mul` chain.
    let s = verify(&gaussian_fixture(), "tmp", BoxShape::Slice, false);
    assert!(s.contains("let mut tmp: ::std::boxed::Box<[i32]> = ::std::vec![0i32; (((nbytes as libc::c_ulong) as usize) / ::core::mem::size_of::<i32>())].into_boxed_slice();"), "{s}");
    assert!(s.contains("::std::mem::drop(tmp);"), "{s}");
    // The census (AST) emission path must annotate the same declarations and
    // the custody instrument must find them by tree (R402-2(a)).
    let outcome = super::rewrite_core_injected(
        ::utils::compilation::str_to_input(&gaussian_fixture()),
        None,
        super::MAX_REVERT_ROUNDS,
        &|_| {},
        false,
        true,
        true,
        Some((
            super::A5Mode::PreciseReplay,
            Some(super::WholeProgramAttestation::FrozenBenchmarkGraph),
        )),
    );
    let super::RewriteOutcome::Emitted { source, .. } = outcome else { panic!("{outcome:?}") };
    for owner in ["tmp", "gaussian_row"] {
        assert!(
            source.contains(&format!("let mut {owner}: ::std::boxed::Box<[i32]> =")),
            "{owner}: {source}"
        );
    }
}

#[test]
fn r395_heman_percentiles_real_shape_recursive_qselect_lend() {
    // `heman_ops_percentiles::{vals, percentiles}` with the real `qselect`:
    // a recursive raw callee that passes the formal (and an offset of it)
    // back to itself; both owners keep their Box and drop at their C free.
    let input = format!(
        r#"{}
unsafe extern "C" fn qselect(mut v: *mut libc::c_float, mut len: libc::c_int, mut k: libc::c_int) -> libc::c_float {{
    let mut i: libc::c_int = 0;
    let mut st: libc::c_int = 0;
    while i < len - 1 as libc::c_int {{
        if !(*v.offset(i as isize) > *v.offset((len - 1 as libc::c_int) as isize)) {{
            let mut f = *v.offset(i as isize);
            *v.offset(i as isize) = *v.offset(st as isize);
            *v.offset(st as isize) = f;
            st += 1;
        }}
        i += 1;
    }}
    let mut __0 = *v.offset((len - 1 as libc::c_int) as isize);
    *v.offset((len - 1 as libc::c_int) as isize) = *v.offset(st as isize);
    *v.offset(st as isize) = __0;
    return if k == st {{ *v.offset(st as isize) }} else if st > k {{ qselect(v, st, k) }} else {{ qselect(v.offset(st as isize), len - st, k - st) }};
}}
pub unsafe extern "C" fn heman_ops_percentiles(mut src: *mut libc::c_float, mut size: libc::c_int, mut nsteps: libc::c_int) -> libc::c_float {{
    let mut npixels = size;
    let mut vals = malloc((::std::mem::size_of::<libc::c_float>() as libc::c_ulong).wrapping_mul(npixels as libc::c_ulong)) as *mut libc::c_float;
    let mut i_0 = 0 as libc::c_int;
    while i_0 < size {{
        *vals.offset(i_0 as isize) = *src.offset(i_0 as isize);
        i_0 += 1;
    }}
    let mut percentiles = malloc((::std::mem::size_of::<libc::c_float>() as libc::c_ulong).wrapping_mul(nsteps as libc::c_ulong)) as *mut libc::c_float;
    let mut tier = 0 as libc::c_int;
    while tier < nsteps {{
        let mut height = qselect(vals, npixels, tier * npixels / nsteps);
        *percentiles.offset(tier as isize) = height;
        tier += 1;
    }}
    free(vals as *mut libc::c_void);
    let mut e = *src;
    let mut tier_0 = nsteps - 1 as libc::c_int;
    while tier_0 >= 0 as libc::c_int {{
        if e > *percentiles.offset(tier_0 as isize) {{
            e = *percentiles.offset(tier_0 as isize);
            break;
        }} else {{ tier_0 -= 1; }}
    }}
    free(percentiles as *mut libc::c_void);
    e
}}"#,
        c_declarations()
    );
    let s = verify(&input, "vals", BoxShape::Slice, false);
    assert!(!s.contains("Box::into_raw"));
    assert!(
        s.contains("qselect(<[_]>::as_mut_ptr(&mut *(vals)), npixels, tier * npixels / nsteps)"),
        "{s}"
    );
    verify(&input, "percentiles", BoxShape::Slice, false);
}

#[test]
fn r399_heman_points_create_real_shape_struct_zero_and_return_transfer() {
    // `heman_points_create::img#5`: `malloc(sizeof(heman_image_s))` cast to the
    // alias `heman_points`, field stores, a nested allocation into a field,
    // and the owner RETURNED raw to the caller (freed in `heman_points_destroy`).
    let input = format!(
        r#"{}
extern "C" {{ fn memcpy(d: *mut libc::c_void, s: *const libc::c_void, n: libc::c_ulong) -> *mut libc::c_void; }}
#[repr(C)] #[derive(Copy, Clone)] pub struct heman_image_s {{ pub width: libc::c_int, pub height: libc::c_int, pub nbands: libc::c_int, pub data: *mut libc::c_float }}
pub type heman_points = heman_image_s;
pub unsafe extern "C" fn heman_points_create(mut xy: *mut libc::c_float, mut npoints: libc::c_int, mut nbands: libc::c_int) -> *mut heman_image_s {{
    let mut img = malloc(::std::mem::size_of::<heman_image_s>() as libc::c_ulong) as *mut heman_points;
    (*img).width = npoints;
    (*img).height = 1 as libc::c_int;
    (*img).nbands = nbands;
    let mut nbytes = (::std::mem::size_of::<libc::c_float>() as libc::c_ulong).wrapping_mul(npoints as libc::c_ulong).wrapping_mul(nbands as libc::c_ulong) as libc::c_int;
    (*img).data = malloc(nbytes as libc::c_ulong) as *mut libc::c_float;
    memcpy((*img).data as *mut libc::c_void, xy as *const libc::c_void, nbytes as libc::c_ulong);
    return img;
}}
pub unsafe extern "C" fn heman_points_destroy(mut victim: *mut heman_points) {{
    free((*victim).data as *mut libc::c_void);
    free(victim as *mut libc::c_void);
}}"#,
        c_declarations()
    );
    let s = verify(&input, "img", BoxShape::Sized, true);
    assert!(
        s.contains("return ::std::boxed::Box::into_raw(img);"),
        "{s}"
    );
    // R412-2: every expression edit must round-trip through the AST
    // emission's graft parser (the pretty printer's spelling, e.g. the
    // trailing comma of a struct literal); a refused graft leaves the source
    // node intact and the program does not compile.
    ::utils::compilation::run_compiler_on_str(&input, |tcx| {
        let (table, _ctx) = super::decide_table_with_ctx_config(
            tcx,
            Some((
                super::A5Mode::PreciseReplay,
                Some(super::WholeProgramAttestation::FrozenBenchmarkGraph),
            )),
        )
        .unwrap();
        let (_, decision) = table
            .entries
            .iter()
            .find(|(s, _)| s.param_name.as_deref() == Some("img"))
            .unwrap();
        let Decision::Box(plan) = decision else { panic!("{decision:?}") };
        for edit in &plan.expr_edits {
            assert!(
                super::ast_transform::graft_expr(&edit.replacement).is_ok(),
                "{}: {}",
                edit.receipt,
                edit.replacement
            );
        }
    })
    .unwrap();
    // A sized owner's `(*img)` reads through the Box unchanged: the plan
    // carries no access edit whose text equals the source (such an edit only
    // claimed the interval and collided with a call bridge composed over the
    // same `memcpy` argument on batch 8's line — main 035).
    ::utils::compilation::run_compiler_on_str(&input, |tcx| {
        let (table, _ctx) = super::decide_table_with_ctx_config(
            tcx,
            Some((
                super::A5Mode::PreciseReplay,
                Some(super::WholeProgramAttestation::FrozenBenchmarkGraph),
            )),
        )
        .unwrap();
        let (_, decision) = table
            .entries
            .iter()
            .find(|(s, _)| s.param_name.as_deref() == Some("img"))
            .unwrap();
        let Decision::Box(plan) = decision else { panic!("{decision:?}") };
        let access: Vec<_> = plan
            .expr_edits
            .iter()
            .filter(|e| e.receipt == "native-box-slice-access")
            .collect();
        assert!(access.is_empty(), "{access:?}");
    })
    .unwrap();
    // The census (AST) path must graft the struct-literal constructor too.
    let outcome = super::rewrite_core_injected(
        ::utils::compilation::str_to_input(&input),
        None,
        super::MAX_REVERT_ROUNDS,
        &|_| {},
        false,
        true,
        true,
        Some((
            super::A5Mode::PreciseReplay,
            Some(super::WholeProgramAttestation::FrozenBenchmarkGraph),
        )),
    );
    let super::RewriteOutcome::Emitted {
        source: census_source,
        ..
    } = outcome
    else {
        panic!("{outcome:?}")
    };
    assert!(census_source.contains("let mut img: ::std::boxed::Box<crate::heman_image_s> = ::std::boxed::Box::new(crate::heman_image_s {"), "{census_source}");
    assert!(
        census_source.contains("return ::std::boxed::Box::into_raw(img);"),
        "{census_source}"
    );
    assert!(s.contains("let mut img: ::std::boxed::Box<crate::heman_image_s> = ::std::boxed::Box::new(crate::heman_image_s { width: 0i32, height: 0i32, nbands: 0i32, data: ::core::ptr::null_mut(), });"), "{s}");
}

#[test]
fn r399_aggregate_owner_with_an_unsupplied_field_holds() {
    // F04: the zero literal is a placeholder only when the program supplies
    // every field itself.
    let input = format!(
        "{} #[repr(C)] #[derive(Copy, Clone)] pub struct Pair {{ pub x: i32, pub y: i32 }} pub unsafe fn f(n: i32) -> i32 {{ let mut p = malloc(core::mem::size_of::<Pair>()) as *mut Pair; (*p).x = n; let v = (*p).x; free(p as *mut core::ffi::c_void); v }}",
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
            .find(|(s, _)| s.param_name.as_deref() == Some("p"))
            .unwrap();
        assert!(matches!(d, Decision::Degraded(_)), "{d:?}");
        assert!(
            ctx.raw_boundary_artifacts
                .ownership_native
                .contains("native-aggregate-fields-supplied"),
            "{}",
            ctx.raw_boundary_artifacts.ownership_native
        );
    })
    .unwrap();
    let supplied = input.replace("(*p).x = n;", "(*p).x = n; (*p).y = n + 1;");
    let s = verify(&supplied, "p", BoxShape::Sized, false);
    assert!(
        s.contains("::std::boxed::Box::new(crate::Pair { x: 0i32, y: 0i32, })"),
        "{s}"
    );
}

#[test]
fn r399_return_transfer_faults_uncovered_live_exit_and_zero_capable_slice() {
    // An early raw-null return while the owner is live is an uncovered exit
    // (the source permit refuses it); a returned boxed slice with a dynamic
    // count could be empty and would hand C `free` a dangling sentinel.
    let uncovered = format!(
        "{} pub unsafe fn make(n: usize) -> *mut u32 {{ let mut buffer = malloc(core::mem::size_of::<u32>()) as *mut u32; *buffer = 1; if n != 0 {{ return buffer; }} 0 as *mut u32 }}",
        declarations()
    );
    ::utils::compilation::run_compiler_on_str(&uncovered, |tcx| {
        let (table, ctx) = super::decide_table_with_ctx_config(
            tcx,
            Some((
                super::A5Mode::PreciseReplay,
                Some(super::WholeProgramAttestation::FrozenBenchmarkGraph),
            )),
        )
        .unwrap();
        let (subject, d) = table
            .entries
            .iter()
            .find(|(s, _)| s.param_name.as_deref() == Some("buffer"))
            .unwrap();
        assert!(matches!(d, Decision::Degraded(_)), "{d:?}");
        let result = super::decision::ownership_fields_source::derive(
            &super::collect_program(tcx),
            subject,
            &ctx.constructions,
        );
        assert!(
            matches!(
                result,
                Err(super::decision::ownership_fields_source::SourceHold::NormalExitCoverage)
            ),
            "{result:?}"
        );
    })
    .unwrap();
    let zero_capable = format!(
        "{} pub unsafe fn make(n: usize) -> *mut u32 {{ let mut buffer = calloc(n, core::mem::size_of::<u32>()) as *mut u32; return buffer; }}",
        declarations()
    );
    ::utils::compilation::run_compiler_on_str(&zero_capable, |tcx| {
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
        assert!(matches!(d, Decision::Degraded(_)), "{d:?}");
        assert!(
            ctx.raw_boundary_artifacts
                .ownership_native
                .contains("native-transfer-nonempty"),
            "{}",
            ctx.raw_boundary_artifacts.ownership_native
        );
    })
    .unwrap();
}

#[test]
fn r401_heman_edt_with_payload_loop_owners_lend_under_native_proofs() {
    // `transform_to_coordfield::pl1#45` / `pl2#53`: two `calloc` owners
    // allocated per loop iteration, written / read through `offset`, lent to
    // the raw callee `edt_with_payload` (which only reads `payload_in` and
    // writes `payload_out` through `offset`), freed at the iteration's end.
    let input = format!(
        r#"{}
pub mod uint {{ pub type uint16_t = u16; }}
use uint::uint16_t;
unsafe extern "C" fn edt_with_payload(mut f: *mut libc::c_float, mut d: *mut libc::c_float, mut z: *mut libc::c_float, mut w: *mut uint16_t, mut n: libc::c_int, mut payload_in: *mut libc::c_float, mut payload_out: *mut libc::c_float) {{
    let mut k = 0 as libc::c_int;
    *w.offset(0 as libc::c_int as isize) = 0 as libc::c_int as uint16_t;
    *z.offset(0 as libc::c_int as isize) = -1.0f32;
    let mut q_0 = 0 as libc::c_int;
    while q_0 < n {{
        while *z.offset((k + 1 as libc::c_int) as isize) < q_0 as libc::c_float {{
            k += 1;
        }}
        *d.offset(q_0 as isize) = ((q_0 - *w.offset(k as isize) as libc::c_int) * (q_0 - *w.offset(k as isize) as libc::c_int)) as libc::c_float + *f.offset(*w.offset(k as isize) as isize);
        *payload_out.offset((q_0 * 2 as libc::c_int) as isize) = *payload_in.offset((*w.offset(k as isize) as libc::c_int * 2 as libc::c_int) as isize);
        *payload_out.offset((q_0 * 2 as libc::c_int + 1 as libc::c_int) as isize) = *payload_in.offset((*w.offset(k as isize) as libc::c_int * 2 as libc::c_int + 1 as libc::c_int) as isize);
        q_0 += 1;
    }}
}}
pub unsafe extern "C" fn transform_to_coordfield(mut data: *mut libc::c_float, mut width: libc::c_int, mut height: libc::c_int, mut ff: *mut libc::c_float, mut dd: *mut libc::c_float, mut zz: *mut libc::c_float, mut ww: *mut uint16_t) {{
    let mut x = 0 as libc::c_int;
    while x < width {{
        let mut pl1 = calloc((height * 2 as libc::c_int) as libc::c_ulong, ::std::mem::size_of::<libc::c_float>() as libc::c_ulong) as *mut libc::c_float;
        let mut pl2 = calloc((height * 2 as libc::c_int) as libc::c_ulong, ::std::mem::size_of::<libc::c_float>() as libc::c_ulong) as *mut libc::c_float;
        let mut f = ff.offset((height * x) as isize);
        let mut d = dd.offset((height * x) as isize);
        let mut z = zz.offset(((height + 1 as libc::c_int) * x) as isize);
        let mut w = ww.offset((height * x) as isize);
        let mut y = 0 as libc::c_int;
        while y < height {{
            *f.offset(y as isize) = *data.offset(((y * width) as isize) + (x as isize));
            *pl1.offset((y * 2 as libc::c_int) as isize) = *data.offset(((2 as libc::c_int * (y * width + x)) as isize) + (0 as libc::c_int as isize));
            *pl1.offset((y * 2 as libc::c_int + 1 as libc::c_int) as isize) = *data.offset(((2 as libc::c_int * (y * width + x)) as isize) + (1 as libc::c_int as isize));
            y += 1;
        }}
        edt_with_payload(f, d, z, w, height, pl1, pl2);
        let mut y_0 = 0 as libc::c_int;
        while y_0 < height {{
            *data.offset(((y_0 * width) as isize) + (x as isize)) = *d.offset(y_0 as isize) + *pl2.offset((2 as libc::c_int * y_0) as isize) + *pl2.offset((2 as libc::c_int * y_0 + 1 as libc::c_int) as isize);
            y_0 += 1;
        }}
        free(pl1 as *mut libc::c_void);
        free(pl2 as *mut libc::c_void);
        x += 1;
    }}
}}"#,
        c_declarations().replace("extern \"C\" { fn malloc", "extern \"C\" { fn calloc(n:libc::c_ulong,s:libc::c_ulong)->*mut libc::c_void; fn malloc")
    );
    // The decision stage admits both owners (the callee proofs and the
    // fresh-allocation peer disjointness hold); the emission stage withdraws
    // them under the raw-boundary signature class of the call, whose sibling
    // arguments `f, d, z, w` are `copy-source-coupled` cursor aliases — the
    // typed frontier this witness pins (`signature-class-held`).
    // Two admissible readings of the composed line (R217-2(a), main 035):
    // on this lane's base the owners DECIDE Box and the emission stage
    // withdraws them under the class; under the batch-8 composition the
    // cursor aliases `f, d` become slice views at an earlier stage, the
    // callee `edt_with_payload` takes a dependency on the held owner class,
    // and the additive stage EXCLUDES the changed candidates of that class —
    // the owners among them — at the ownership stage (R397-6(a)), named by
    // the receipt `exclusion-rederivation:…:new-family-dependency:…`.
    #[derive(Clone, Copy, PartialEq, Debug)]
    enum Reading {
        DecidedBox,
        ExcludedWithDependency,
    }
    let decided = |owner: &str| -> Reading {
        ::utils::compilation::run_compiler_on_str(&input, |tcx| {
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
                .find(|(s, _)| s.param_name.as_deref() == Some(owner))
                .unwrap();
            match decision {
                Decision::Box(plan) => {
                    assert_eq!(plan.shape, BoxShape::Slice);
                    assert!(
                        plan.receipts
                            .iter()
                            .any(|r| r.contains("disjoint=fresh-allocation-derivation-closure")),
                        "{:?}",
                        plan.receipts
                    );
                    Reading::DecidedBox
                }
                Decision::Degraded(_) => {
                    let key = subject.identity_key("transform_to_coordfield");
                    let receipt = ctx
                        .raw_boundary_artifacts
                        .additive_family_receipts
                        .iter()
                        .find(|r| {
                            r.family == "Ownership"
                                && r.owner_path == "transform_to_coordfield"
                                && r.cause.starts_with("exclusion-rederivation:")
                                && r.cause.contains(":new-family-dependency:")
                                && r.subjects.iter().any(|(s, _, _)| *s == key)
                        });
                    assert!(
                        receipt.is_some(),
                        "{owner}: {decision:?}\n{:?}",
                        ctx.raw_boundary_artifacts.additive_family_receipts
                    );
                    Reading::ExcludedWithDependency
                }
                Decision::Ref { .. }
                | Decision::InferredRef { .. }
                | Decision::Slice { .. }
                | Decision::NestedSlice { .. }
                | Decision::Cursor { .. }
                | Decision::Opt { .. } => panic!("{owner}: {decision:?}"),
            }
        })
        .unwrap()
    };
    let reading = decided("pl1");
    assert_eq!(decided("pl2"), reading);
    let outcome = super::rewrite_core_injected(
        ::utils::compilation::str_to_input(&input),
        None,
        super::MAX_REVERT_ROUNDS,
        &|_| {},
        false,
        true,
        true,
        Some((
            super::A5Mode::PreciseReplay,
            Some(super::WholeProgramAttestation::FrozenBenchmarkGraph),
        )),
    );
    let super::RewriteOutcome::Emitted {
        degradations,
        e1_subject_receipt,
        raw_boundary_artifacts,
        source,
        reverted_count,
        ..
    } = outcome
    else {
        panic!("{outcome:?}")
    };
    for owner in [
        "transform_to_coordfield::pl1#13",
        "transform_to_coordfield::pl2#21",
    ] {
        // A withdrawn Box row degrades under its identity key (`…#13`); a
        // row degraded at decision under the plain label.
        let label = owner.split('#').next().unwrap();
        let Some(row) = degradations
            .iter()
            .find(|d| d.subject == owner || d.subject == label)
        else {
            // The third reading (batch 8's dry3, wave-6s 011): the decided
            // Box DELIVERS — the class no longer holds on its siblings.
            assert_eq!(reading, Reading::DecidedBox, "{owner}");
            assert_eq!(reverted_count, 0, "{source}");
            assert!(
                source.contains(&format!(
                    "let mut {label_name}: ::std::boxed::Box<[f32]> =",
                    label_name = label.rsplit("::").next().unwrap()
                )),
                "{owner}: {source}"
            );
            assert!(
                source.contains(&format!(
                    "::std::mem::drop({})",
                    label.rsplit("::").next().unwrap()
                )),
                "{owner}: {source}"
            );
            continue;
        };
        let seed = e1_subject_receipt
            .lines()
            .find(|line| line.starts_with(&format!("{owner}\t")))
            .unwrap_or_else(|| panic!("{owner} seed row: {e1_subject_receipt}"));
        let columns: Vec<&str> = seed.split('\t').collect();
        assert_eq!(columns[7], "degraded", "{seed}");
        assert_eq!(columns[11], "0", "{seed}");
        match reading {
            Reading::DecidedBox => {
                assert_eq!(
                    row.reason.key(),
                    "signature-class-held",
                    "{owner}: {}",
                    row.reason.detail()
                );
                assert!(
                    row.reason.detail().contains("copy-source-coupled"),
                    "{}",
                    row.reason.detail()
                );
                // R402-2(b): the withdrawn Box row is DEGRADED in the E1 seed
                // with its withdrawal reason (never a placed box row) and is
                // no custody expectation, so the strict instrument sees no
                // inferred-type claim.
                assert_eq!(columns[8], "box-withdrawn-at-emission", "{seed}");
                assert!(columns[9].starts_with("signature-class-held:"), "{seed}");
            }
            Reading::ExcludedWithDependency => {
                // Excluded before emission: the row degrades on its own
                // (prior) reason and never becomes a Box row anywhere.
                assert_ne!(row.reason.key(), "signature-class-held", "{owner}");
                assert_ne!(columns[8], "box-withdrawn-at-emission", "{seed}");
            }
        }
        assert!(
            !raw_boundary_artifacts
                .custody_expectations
                .iter()
                .any(|e| e.subject_key == owner),
            "{owner} must not be a custody expectation"
        );
    }
}

#[test]
fn r401_peer_derived_from_the_subject_is_not_disjoint() {
    // `callee(p, p.offset(1))`: the second peer is derived from the subject's
    // own allocation. The source permit already refuses every alias-forming
    // use of the root, so the native closure's premise (no peer derived from
    // the allocation) is enforced upstream; this control pins that refusal.
    let input = format!(
        "{} unsafe fn pair(a: *mut u32, b: *mut u32) {{ *a += *b; }} pub unsafe fn prepare() -> u32 {{ let mut buffer = calloc(4, core::mem::size_of::<u32>()) as *mut u32; *buffer = 1; pair(buffer, buffer.offset(1)); let value = *buffer; free(buffer as *mut core::ffi::c_void); value }}",
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
        assert!(matches!(d, Decision::Degraded(_)), "{d:?}");
        assert!(
            ctx.raw_boundary_artifacts
                .ownership_native
                .contains("\tSource::UnsupportedOwnerUse\t"),
            "{}",
            ctx.raw_boundary_artifacts.ownership_native
        );
    })
    .unwrap();
}

#[test]
fn r403_heman_elevations_pointer_array_owner_depth_two() {
    // `heman_generate_archipelago_political_3::elevations#9`: a `malloc`ed
    // array of raw pointers (`*mut *mut heman_image`), filled by index from a
    // producer, read through `(**elevations.offset(i)).data`, each element
    // destroyed by a callee, the array freed. The outer owner becomes
    // `Box<[*mut heman_image_s]>`; the inner pointers stay raw.
    let input = format!(
        r#"{}
#[repr(C)] #[derive(Copy, Clone)] pub struct heman_image_s {{ pub width: libc::c_int, pub data: *mut libc::c_float }}
pub type heman_image = heman_image_s;
unsafe extern "C" fn make(mut width: libc::c_int) -> *mut heman_image {{
    let mut img = malloc(::std::mem::size_of::<heman_image_s>() as libc::c_ulong) as *mut heman_image;
    (*img).width = width;
    (*img).data = malloc((::std::mem::size_of::<libc::c_float>() as libc::c_ulong).wrapping_mul(width as libc::c_ulong)) as *mut libc::c_float;
    return img;
}}
unsafe extern "C" fn heman_image_destroy(mut img: *mut heman_image) {{
    free((*img).data as *mut libc::c_void);
    free(img as *mut libc::c_void);
}}
pub unsafe extern "C" fn political_3(mut width: libc::c_int, mut ncolors: libc::c_int) -> libc::c_float {{
    let mut elevations = malloc((::std::mem::size_of::<*mut heman_image>() as libc::c_ulong).wrapping_mul(ncolors as libc::c_ulong)) as *mut *mut heman_image;
    let mut cindex = 0 as libc::c_int;
    while cindex < ncolors {{
        *elevations.offset(cindex as isize) = make(width);
        cindex += 1;
    }}
    let mut acc = 0.0f32;
    let mut cindex_0 = 0 as libc::c_int;
    while cindex_0 < ncolors {{
        let mut src = ((**elevations.offset(cindex_0 as isize)).data).offset(0 as isize);
        acc += *src;
        heman_image_destroy(*elevations.offset(cindex_0 as isize));
        cindex_0 += 1;
    }}
    free(elevations as *mut libc::c_void);
    acc
}}"#,
        c_declarations()
    );
    let s = verify(&input, "elevations", BoxShape::Slice, false);
    assert!(s.contains("let mut elevations: ::std::boxed::Box<[*mut crate::heman_image_s]> = ::std::vec![::core::ptr::null_mut(); "), "{s}");
    assert!(
        s.contains("heman_image_destroy(elevations[(cindex_0) as usize]);"),
        "{s}"
    );
    // Control: only one owned level is admitted; a `*mut *mut *mut` owner
    // (a table of pointer tables) stays outside the permit.
    let deeper = format!(
        "{} pub unsafe fn table(n: usize) -> usize {{ let mut t = malloc((core::mem::size_of::<*mut *mut u32>() as libc::c_ulong).wrapping_mul(n as libc::c_ulong)) as *mut *mut *mut u32; *t.offset(0) = core::ptr::null_mut(); let v = (*t.offset(0)).is_null() as usize; free(t as *mut libc::c_void); v }}",
        c_declarations()
    );
    ::utils::compilation::run_compiler_on_str(&deeper, |tcx| {
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
            .find(|(s, _)| s.param_name.as_deref() == Some("t") && s.ptr_depth == 3)
            .unwrap();
        assert!(matches!(d, Decision::Degraded(_)), "{d:?}");
        let _ = &ctx;
    })
    .unwrap();
}

#[test]
fn r402_annotated_binding_stays_held_without_an_ast_declaration_channel() {
    // bzip2 spells its owners `let mut v: *mut T = malloc(..)`: the AST
    // emission has no channel to replace a declared type by a Box type, so
    // the owner is a typed hold (`native-annotated-binding`).
    let input = format!(
        "{} pub unsafe fn prepare(n: usize) -> u32 {{ let mut buffer: *mut u32 = calloc(4, core::mem::size_of::<u32>()) as *mut u32; *buffer.offset(1) = 9; let value = *buffer.offset(1); free(buffer as *mut core::ffi::c_void); value }}",
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
        assert!(matches!(d, Decision::Degraded(_)), "{d:?}");
        assert!(
            ctx.raw_boundary_artifacts
                .ownership_native
                .contains("native-annotated-binding"),
            "{}",
            ctx.raw_boundary_artifacts.ownership_native
        );
    })
    .unwrap();
}

#[test]
fn r402_probe_nested_module_alias_struct_owner_census_path() {
    // Corpus-shaped modules: the struct lives in `src::src::color`, the owner
    // in `src::src::points`, the site names it only through the alias.
    let input = format!(
        r#"{}
pub mod src {{ pub mod src {{
pub mod color {{
    #[repr(C)] #[derive(Copy, Clone)] pub struct heman_image_s {{ pub width: crate::libc::c_int, pub height: crate::libc::c_int, pub nbands: crate::libc::c_int, pub data: *mut crate::libc::c_float }}
    pub type heman_image = heman_image_s;
}}
pub mod points {{
    use crate::src::src::color::heman_image;
    use crate::libc;
    pub type heman_points = crate::src::src::color::heman_image_s;
    extern "C" {{ fn malloc(n: libc::c_ulong) -> *mut libc::c_void; fn memcpy(d: *mut libc::c_void, s: *const libc::c_void, n: libc::c_ulong) -> *mut libc::c_void; }}
    #[no_mangle]
    pub unsafe extern "C" fn heman_points_create(mut xy:
            *mut libc::c_float, mut npoints: libc::c_int,
        mut nbands: libc::c_int) -> *mut heman_image {{
        let mut img =
            malloc(::std::mem::size_of::<heman_image>() as
                        libc::c_ulong) as *mut heman_points;
        (*img).width = npoints;
        (*img).height = 1 as libc::c_int;
        (*img).nbands = nbands;
        let mut nbytes =
            (::std::mem::size_of::<libc::c_float>() as
                                libc::c_ulong).wrapping_mul(npoints as
                            libc::c_ulong).wrapping_mul(nbands as libc::c_ulong) as
                libc::c_int;
        (*img).data =
            malloc(nbytes as libc::c_ulong) as *mut libc::c_float;
        memcpy((*img).data as *mut libc::c_void,
            xy as *const libc::c_void, nbytes as libc::c_ulong);
        return img;
    }}
}}
}} }}"#,
        c_declarations()
    );
    let outcome = super::rewrite_core_injected(
        ::utils::compilation::str_to_input(&input),
        None,
        super::MAX_REVERT_ROUNDS,
        &|_| {},
        false,
        true,
        true,
        Some((
            super::A5Mode::PreciseReplay,
            Some(super::WholeProgramAttestation::FrozenBenchmarkGraph),
        )),
    );
    let super::RewriteOutcome::Emitted {
        source,
        degradations,
        first_diags,
        ..
    } = outcome
    else {
        panic!("{outcome:?}")
    };
    println!(
        "R402_PROBE degradations={:?} diags={first_diags:?}\n{source}",
        degradations
            .iter()
            .map(|d| (d.subject.clone(), d.reason.key(), d.reason.detail()))
            .collect::<Vec<_>>()
    );
    assert!(
        source.contains("::std::boxed::Box::new(crate::src::src::color::heman_image_s {"),
        "{source}"
    );
}

#[test]
fn r402_real_heman_ops_percentiles_body_delivers_both_owners() {
    // The verbatim corpus bodies of `heman_ops_percentiles` and `qselect`,
    // with the program's types and foreign helpers declared around them.
    // The census of `860b4fa7` held both owners: the assertion messages are
    // `&'static` byte-string literals (exempt from the whole-caller reference
    // rule) and `__assert_fail` is a diverging call (a path that never
    // returns and neither frees nor drops the owner).
    let input = format!(
        r#"{}
pub type heman_color = libc::c_uint;
#[repr(C)] #[derive(Copy, Clone)] pub struct heman_image_s {{ pub width: libc::c_int, pub height: libc::c_int, pub nbands: libc::c_int, pub data: *mut libc::c_float }}
pub type heman_image = heman_image_s;
extern "C" {{ fn __assert_fail(a: *const libc::c_char, f: *const libc::c_char, l: libc::c_uint, fun: *const libc::c_char) -> !; }}
unsafe extern "C" fn _match(mut mask: *mut heman_image, mut mask_color: heman_color, mut invert_mask: libc::c_int, mut pixel_index: libc::c_int) -> libc::c_int {{
    let mut mcolor = ((*mask).data).offset((pixel_index * 3 as libc::c_int) as isize);
    ((*mcolor.offset(0 as isize) > 0.5f32) as libc::c_int) ^ invert_mask
}}
{}"#,
        c_declarations().replace("pub mod libc { pub use core::ffi::c_int;", "pub mod libc { pub use core::ffi::c_char; pub use core::ffi::c_uint; pub use core::ffi::c_uchar; pub use core::ffi::c_int;"),
        HEMAN_OPS_PERCENTILES_BODY
    );
    // Both owners DECIDE Box; the emission stage withdraws them under the
    // function's signature class (`blocked-subject:kind-raw` — the raw
    // parameters `hmap`, `mask`), the same frontier as the `edt_with_payload`
    // owners (report 016 STOP 1).
    ::utils::compilation::run_compiler_on_str(&input, |tcx| {
        let (table, _ctx) = super::decide_table_with_ctx_config(
            tcx,
            Some((
                super::A5Mode::PreciseReplay,
                Some(super::WholeProgramAttestation::FrozenBenchmarkGraph),
            )),
        )
        .unwrap();
        for name in ["vals", "percentiles"] {
            let (_, decision) = table
                .entries
                .iter()
                .find(|(s, _)| s.param_name.as_deref() == Some(name))
                .unwrap();
            assert!(
                matches!(decision, Decision::Box(plan) if plan.shape == BoxShape::Slice),
                "{name}: {decision:?}"
            );
        }
    })
    .unwrap();
    let outcome = super::rewrite_core_injected(
        ::utils::compilation::str_to_input(&input),
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
        degradations,
        source,
        reverted_count,
        ..
    } = outcome
    else {
        panic!("{outcome:?}")
    };
    // Two admissible readings (R217-2(a), main 035): on this lane's base the
    // owner class holds on the raw parameters (`blocked-subject:kind-raw`)
    // and both owners are withdrawn; under the batch-8 composition
    // (wave-5d's per-subject scope) the raw siblings no longer hold the
    // class and both owners DELIVER — `Box<[f32]>` on the binding, the C
    // frees as drops, the callee lent raw (its class is held:
    // `qselect::v` is a Box-parameter candidate that lends).
    let held = |owner: &str| degradations.iter().find(|d| d.subject == owner).cloned();
    match (
        held("heman_ops_percentiles::vals#292"),
        held("heman_ops_percentiles::percentiles#328"),
    ) {
        (Some(vals), Some(percentiles)) => {
            for row in [vals, percentiles] {
                assert_eq!(
                    row.reason.key(),
                    "signature-class-held",
                    "{}: {}",
                    row.subject,
                    row.reason.detail()
                );
                assert!(
                    row.reason.detail().contains("blocked-subject:kind-raw"),
                    "{}",
                    row.reason.detail()
                );
            }
        }
        (None, None) => {
            assert_eq!(reverted_count, 0, "{source}");
            for owner in ["vals", "percentiles"] {
                assert!(
                    source.contains(&format!("let mut {owner}: ::std::boxed::Box<[f32]> =")),
                    "{owner}: {source}"
                );
                assert!(
                    source.contains(&format!("::std::mem::drop({owner})")),
                    "{owner}: {source}"
                );
            }
            assert!(
                source.contains(
                    "qselect(<[_]>::as_mut_ptr(&mut *(vals)), npixels, tier * npixels / nsteps)"
                ),
                "{source}"
            );
        }
        (vals, percentiles) => panic!("one owner delivered, one held: {vals:?} {percentiles:?}"),
    }
}

#[test]
fn r412_real_political_3_elevations_verbatim_body() {
    // The verbatim corpus `heman_generate_archipelago_political_3` up to the
    // owner's free (`elevations#9`, rule K): the pointer array is filled from
    // a producer, read through `(**elevations.offset(i)).data` as the BASE of
    // a cursor `src` that another family turns into a slice, each element
    // destroyed by a local callee, the array freed. main 037's heman probe
    // failed to compile this row (R412-2): the count's element path was not
    // crate-rooted, and the access under the cursor's initializer kept
    // `.offset` on the Box.
    let input = format!(
        r#"{}
#[repr(C)] #[derive(Copy, Clone)] pub struct heman_image_s {{ pub width: libc::c_int, pub height: libc::c_int, pub nbands: libc::c_int, pub data: *mut libc::c_float }}
pub type heman_image = heman_image_s;
#[repr(C)] #[derive(Copy, Clone)] pub struct heman_color_s {{ pub r: libc::c_int }}
pub type heman_color = heman_color_s;
extern "C" {{ fn heman_generate_archipelago_political_2(w: libc::c_int, h: libc::c_int, c: heman_color, seed: libc::c_int, political: *mut heman_image, invert: libc::c_int) -> *mut heman_image; fn heman_image_create(w: libc::c_int, h: libc::c_int, n: libc::c_int) -> *mut heman_image; fn heman_image_clear(img: *mut heman_image, v: libc::c_float); }}
pub unsafe extern "C" fn heman_image_destroy(mut img: *mut heman_image) {{
    free((*img).data as *mut libc::c_void);
    free(img as *mut libc::c_void);
}}
{}"#,
        c_declarations(),
        POLITICAL_3_BODY
    );
    // Two admissible readings (R217-2(a)): on this base `src` stays raw and
    // the owner DELIVERS (the count's element path crate-rooted — R412-2(i));
    // on the batch-8 composition the slice family constructs `src` over the
    // owner access and the owner HOLDS `native-access-under-slice-construction`
    // (R412-2(ii)) instead of emitting `.offset` on the Box.
    let held = ::utils::compilation::run_compiler_on_str(&input, |tcx| {
        let (table, ctx) = super::decide_table_with_ctx_config(
            tcx,
            Some((
                super::A5Mode::PreciseReplay,
                Some(super::WholeProgramAttestation::FrozenBenchmarkGraph),
            )),
        )
        .unwrap();
        let (_, decision) = table
            .entries
            .iter()
            .find(|(s, _)| s.param_name.as_deref() == Some("elevations"))
            .unwrap();
        let row = ctx
            .raw_boundary_artifacts
            .ownership_native
            .lines()
            .find(|row| row.starts_with("heman_generate_archipelago_political_3::elevations#"))
            .unwrap()
            .to_owned();
        match decision {
            Decision::Box(plan) => {
                assert_eq!(plan.shape, BoxShape::Slice);
                false
            }
            Decision::Degraded(_) => {
                assert!(
                    row.contains("\theld\t")
                        && row.contains("native-access-under-slice-construction"),
                    "{row}"
                );
                true
            }
            Decision::Ref { .. }
            | Decision::InferredRef { .. }
            | Decision::Slice { .. }
            | Decision::NestedSlice { .. }
            | Decision::Cursor { .. }
            | Decision::Opt { .. } => panic!("{decision:?}"),
        }
    })
    .unwrap();
    if held {
        return;
    }
    let s = verify(&input, "elevations", BoxShape::Slice, false);
    assert!(
        s.contains("/ ::core::mem::size_of::<*mut crate::heman_image_s>())].into_boxed_slice();"),
        "{s}"
    );
    assert!(!s.contains("elevations.offset("), "{s}");
    assert!(
        s.contains("heman_image_destroy(elevations[(cindex_0) as usize]);"),
        "{s}"
    );
    assert!(s.contains("::std::mem::drop(elevations);"), "{s}");
}

const POLITICAL_3_BODY: &str = r#"pub unsafe extern "C" fn heman_generate_archipelago_political_3(
    mut width: libc::c_int,
    mut height: libc::c_int,
    mut colors: *const heman_color,
    mut ncolors: libc::c_int,
    mut ocean: heman_color,
    mut seed: libc::c_int,
    mut political: *mut heman_image,
) -> *mut heman_image {
    let mut elevations = malloc(
        (::std::mem::size_of::<*mut heman_image>() as libc::c_ulong)
            .wrapping_mul(ncolors as libc::c_ulong),
    ) as *mut *mut heman_image;
    let mut cindex = 0 as libc::c_int;
    while cindex < ncolors {
        *elevations.offset(cindex as isize) = heman_generate_archipelago_political_2(
            width,
            height,
            *colors.offset(cindex as isize),
            seed,
            political,
            1 as libc::c_int,
        );
        cindex += 1;
    }
    let mut elevation = heman_image_create(width, height, 1 as libc::c_int);
    heman_image_clear(elevation, 0 as libc::c_int as libc::c_float);
    let mut cindex_0 = 0 as libc::c_int;
    while cindex_0 < ncolors {
        let mut y: libc::c_int = 0;
        y = 0 as libc::c_int;
        while y < height {
            let mut dst = ((*elevation).data).offset((y * width) as isize);
            let mut src = ((**elevations.offset(cindex_0 as isize)).data)
                .offset((y * width) as isize);
            let mut x = 0 as libc::c_int;
            while x < width {
                *dst = if *src > *dst { *src } else { *dst };
                x += 1;
                dst = dst.offset(1);
                src = src.offset(1);
            }
            y += 1;
        }
        heman_image_destroy(*elevations.offset(cindex_0 as isize));
        cindex_0 += 1;
    }
    free(elevations as *mut libc::c_void);
    return elevation;
}"#;

const HEMAN_OPS_PERCENTILES_BODY: &str = r#"pub unsafe extern "C" fn heman_ops_percentiles(mut hmap:
        *mut heman_image, mut nsteps: libc::c_int,
    mut mask: *mut heman_image, mut mask_color: heman_color,
    mut invert_mask: libc::c_int, mut offset: libc::c_float)
    -> *mut heman_image {
    if (*hmap).nbands == 1 as libc::c_int
        {} else {
        __assert_fail(b"hmap->nbands == 1\0" as *const u8 as
                *const libc::c_char,
            b"../src/ops.c\0" as *const u8 as *const libc::c_char,
            427 as libc::c_int as libc::c_uint,
            ([b'h' as i8, b'e' as i8, b'm' as i8, b'a' as i8,
                            b'n' as i8, b'_' as i8, b'i' as i8, b'm' as i8, b'a' as i8,
                            b'g' as i8, b'e' as i8, b' ' as i8, b'*' as i8, b'h' as i8,
                            b'e' as i8, b'm' as i8, b'a' as i8, b'n' as i8, b'_' as i8,
                            b'o' as i8, b'p' as i8, b's' as i8, b'_' as i8, b'p' as i8,
                            b'e' as i8, b'r' as i8, b'c' as i8, b'e' as i8, b'n' as i8,
                            b't' as i8, b'i' as i8, b'l' as i8, b'e' as i8, b's' as i8,
                            b'(' as i8, b'h' as i8, b'e' as i8, b'm' as i8, b'a' as i8,
                            b'n' as i8, b'_' as i8, b'i' as i8, b'm' as i8, b'a' as i8,
                            b'g' as i8, b'e' as i8, b' ' as i8, b'*' as i8, b',' as i8,
                            b' ' as i8, b'i' as i8, b'n' as i8, b't' as i8, b',' as i8,
                            b' ' as i8, b'h' as i8, b'e' as i8, b'm' as i8, b'a' as i8,
                            b'n' as i8, b'_' as i8, b'i' as i8, b'm' as i8, b'a' as i8,
                            b'g' as i8, b'e' as i8, b' ' as i8, b'*' as i8, b',' as i8,
                            b' ' as i8, b'h' as i8, b'e' as i8, b'm' as i8, b'a' as i8,
                            b'n' as i8, b'_' as i8, b'c' as i8, b'o' as i8, b'l' as i8,
                            b'o' as i8, b'r' as i8, b',' as i8, b' ' as i8, b'i' as i8,
                            b'n' as i8, b't' as i8, b',' as i8, b' ' as i8, b'f' as i8,
                            b'l' as i8, b'o' as i8, b'a' as i8, b't' as i8, b')' as i8,
                            b'\0' as i8]).as_ptr());
    }
    if mask.is_null() || (*mask).nbands == 3 as libc::c_int
        {} else {
        __assert_fail(b"!mask || mask->nbands == 3\0" as *const u8
                as *const libc::c_char,
            b"../src/ops.c\0" as *const u8 as *const libc::c_char,
            428 as libc::c_int as libc::c_uint,
            ([b'h' as i8, b'e' as i8, b'm' as i8, b'a' as i8,
                            b'n' as i8, b'_' as i8, b'i' as i8, b'm' as i8, b'a' as i8,
                            b'g' as i8, b'e' as i8, b' ' as i8, b'*' as i8, b'h' as i8,
                            b'e' as i8, b'm' as i8, b'a' as i8, b'n' as i8, b'_' as i8,
                            b'o' as i8, b'p' as i8, b's' as i8, b'_' as i8, b'p' as i8,
                            b'e' as i8, b'r' as i8, b'c' as i8, b'e' as i8, b'n' as i8,
                            b't' as i8, b'i' as i8, b'l' as i8, b'e' as i8, b's' as i8,
                            b'(' as i8, b'h' as i8, b'e' as i8, b'm' as i8, b'a' as i8,
                            b'n' as i8, b'_' as i8, b'i' as i8, b'm' as i8, b'a' as i8,
                            b'g' as i8, b'e' as i8, b' ' as i8, b'*' as i8, b',' as i8,
                            b' ' as i8, b'i' as i8, b'n' as i8, b't' as i8, b',' as i8,
                            b' ' as i8, b'h' as i8, b'e' as i8, b'm' as i8, b'a' as i8,
                            b'n' as i8, b'_' as i8, b'i' as i8, b'm' as i8, b'a' as i8,
                            b'g' as i8, b'e' as i8, b' ' as i8, b'*' as i8, b',' as i8,
                            b' ' as i8, b'h' as i8, b'e' as i8, b'm' as i8, b'a' as i8,
                            b'n' as i8, b'_' as i8, b'c' as i8, b'o' as i8, b'l' as i8,
                            b'o' as i8, b'r' as i8, b',' as i8, b' ' as i8, b'i' as i8,
                            b'n' as i8, b't' as i8, b',' as i8, b' ' as i8, b'f' as i8,
                            b'l' as i8, b'o' as i8, b'a' as i8, b't' as i8, b')' as i8,
                            b'\0' as i8]).as_ptr());
    }
    let mut size = (*hmap).height * (*hmap).width;
    let mut src = (*hmap).data;
    let mut minv = 1000 as libc::c_int as libc::c_float;
    let mut maxv = -(1000 as libc::c_int) as libc::c_float;
    let mut npixels = 0 as libc::c_int;
    let mut i = 0 as libc::c_int;
    while i < size {
        if mask.is_null() ||
                _match(mask, mask_color, invert_mask, i) != 0 {
            minv =
                if minv > *src.offset(i as isize) {
                    *src.offset(i as isize)
                } else { minv };
            maxv =
                if maxv > *src.offset(i as isize) {
                    maxv
                } else { *src.offset(i as isize) };
            npixels += 1;
        }
        i += 1;
    }
    let mut vals =
        malloc((::std::mem::size_of::<libc::c_float>() as
                            libc::c_ulong).wrapping_mul(npixels as libc::c_ulong)) as
            *mut libc::c_float;
    npixels = 0 as libc::c_int;
    let mut i_0 = 0 as libc::c_int;
    while i_0 < size {
        if mask.is_null() ||
                _match(mask, mask_color, invert_mask, i_0) != 0 {
            let fresh20 = npixels;
            npixels = npixels + 1;
            *vals.offset(fresh20 as isize) = *src.offset(i_0 as isize);
        }
        i_0 += 1;
    }
    let mut percentiles =
        malloc((::std::mem::size_of::<libc::c_float>() as
                            libc::c_ulong).wrapping_mul(nsteps as libc::c_ulong)) as
            *mut libc::c_float;
    let mut tier = 0 as libc::c_int;
    while tier < nsteps {
        let mut height =
            qselect(vals, npixels, tier * npixels / nsteps);
        *percentiles.offset(tier as isize) = height;
        tier += 1;
    }
    free(vals as *mut libc::c_void);
    let mut i_1 = 0 as libc::c_int;
    while i_1 < size {
        let mut e = *src;
        if mask.is_null() ||
                _match(mask, mask_color, invert_mask, i_1) != 0 {
            let mut tier_0 = nsteps - 1 as libc::c_int;
            while tier_0 >= 0 as libc::c_int {
                if e > *percentiles.offset(tier_0 as isize) {
                    e = *percentiles.offset(tier_0 as isize);
                    break;
                } else { tier_0 -= 1; }
            }
        }
        *src = e + offset;
        let fresh21 = *src;
        src = src.offset(1);
        i_1 += 1;
    }
    free(percentiles as *mut libc::c_void);
    return hmap;
}
unsafe extern "C" fn qselect(mut v: *mut libc::c_float,
    mut len: libc::c_int, mut k: libc::c_int) -> libc::c_float {
    let mut i: libc::c_int = 0;
    let mut st: libc::c_int = 0;
    i = 0 as libc::c_int;
    st = i;
    while i < len - 1 as libc::c_int {
        if !(*v.offset(i as isize) >
                        *v.offset((len - 1 as libc::c_int) as isize)) {
            let mut f = *v.offset(i as isize);
            *v.offset(i as isize) = *v.offset(st as isize);
            *v.offset(st as isize) = f;
            st += 1;
        }
        i += 1;
    }
    let mut __0 = *v.offset((len - 1 as libc::c_int) as isize);
    *v.offset((len - 1 as libc::c_int) as isize) =
        *v.offset(st as isize);
    *v.offset(st as isize) = __0;
    return if k == st {
            *v.offset(st as isize)
        } else if st > k {
            qselect(v, st, k)
        } else { qselect(v.offset(st as isize), len - st, k - st) };
}"#;

#[test]
fn r407_real_transform_to_distance_view_aliases_meet_the_owner_class_hold() {
    // The verbatim corpus `transform_to_distance` + `edt`: four `calloc`
    // owners whose every use is through a per-iteration alias
    // `let mut f = ff.offset(height * x)` (written/read as `*f.offset(y)`,
    // passed raw to `edt`), freed at the end. The native producer admits the
    // alias as a runtime-checked mutable view over the owner (R394-1) and
    // derives a bundle for every owner; the seam plans no call glue at the
    // lent alias arguments (the lend is the argument text) and `edt`'s
    // interface takes a dependency on the owner's class. The frontier is
    // that class: the alias subjects stay `Degraded(copy-source-coupled)`
    // siblings with a c-arm requirement, which holds the whole owner class
    // (`blocked-subject:copy-source-coupled`, `missing-required-arm:c`) —
    // the sibling hold R407-12 exempts a local-only Box plan from (wave-5d's
    // per-subject scope). Pinned: no interval collision, every bundle
    // derived, the dependency taken, the owners withdrawn with the class.
    let input = format!(
        r#"{}
pub mod uint {{ pub type uint16_t = u16; }}
use uint::uint16_t;
#[repr(C)] #[derive(Copy, Clone)] pub struct heman_image_s {{ pub width: libc::c_int, pub height: libc::c_int, pub nbands: libc::c_int, pub data: *mut libc::c_float }}
pub type heman_image = heman_image_s;
pub static mut INF: libc::c_float = 1E20f64 as libc::c_float;
{}"#,
        c_declarations().replace("extern \"C\" { fn malloc", "extern \"C\" { fn calloc(n:libc::c_ulong,s:libc::c_ulong)->*mut libc::c_void; fn malloc"),
        TRANSFORM_TO_DISTANCE_BODY
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
        for name in ["ff", "dd", "zz", "ww"] {
            let (subject, decision) = table
                .entries
                .iter()
                .find(|(s, _)| s.param_name.as_deref() == Some(name))
                .unwrap();
            let slot = ctx.slots.fn_local_slots[&subject.fn_did]
                .slot_for_local_depth(subject.local, 0)
                .unwrap();
            assert_eq!(
                ctx.model.get(&super::SlotRef::Local(subject.fn_did, slot)),
                Some(&super::SlotKind::Owning),
                "{name}: actual model grant"
            );
            // The native bundle exists (the alias permit admitted every use);
            // the final decision does not carry it.
            let row = ctx
                .raw_boundary_artifacts
                .ownership_native
                .lines()
                .find(|row| row.starts_with(&format!("transform_to_distance::{name}#")))
                .unwrap_or_else(|| panic!("{name}: no native audit row"));
            assert!(
                row.contains("\ttrue\tnot-selected\tCandidateNotSelected\t"),
                "{name}: {row}"
            );
            assert!(
                matches!(decision, Decision::Degraded(_)),
                "{name}: {decision:?}"
            );
        }
        let ownership_receipts = ctx
            .raw_boundary_artifacts
            .additive_family_receipts
            .iter()
            .filter(|r| r.family == "Ownership")
            .map(|r| format!("{}: {}", r.owner_path, r.cause))
            .collect::<Vec<_>>();
        assert!(
            ownership_receipts
                .iter()
                .all(|cause| !cause.contains("newer-family-collision")),
            "{ownership_receipts:?}"
        );
        assert!(
            ownership_receipts
                .iter()
                .any(|cause| cause.starts_with("edt: new-family-dependency:")),
            "{ownership_receipts:?}"
        );
        assert!(
            ownership_receipts
                .iter()
                .any(|cause| cause.starts_with("transform_to_distance: ")),
            "{ownership_receipts:?}"
        );
    })
    .unwrap();
}

#[test]
fn r407_per_iteration_alias_is_admitted_and_its_owner_class_holds() {
    // The `transform_to_*` shape in miniature: a per-iteration alias
    // `let mut row = buffer.offset(x * 4)` is the only handle on the owner
    // inside the loop (written, read, passed to a local callee whose formal
    // is a live shared slice). The alias permit derives the bundle; the seam
    // plans no glue at the lent alias argument; the owner class holds on the
    // alias sibling (`blocked-subject:copy-source-coupled`) — the exact
    // R407-12 frontier, named in the ownership-stage receipt.
    let input = format!(
        "{} unsafe fn read(p:*mut u32, k:usize)->u32 {{ *p.offset(k as isize) }} pub unsafe fn prepare()->u32 {{ let mut buffer=calloc(8,core::mem::size_of::<u32>()) as *mut u32; let mut x=0isize; let mut total=0; while x<2 {{ let mut row=buffer.offset(x*4); *row.offset(1)=9; total+=read(row, 1); x+=1; }} free(buffer as *mut core::ffi::c_void); total }}",
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
        let (_, decision) = table
            .entries
            .iter()
            .find(|(s, _)| s.param_name.as_deref() == Some("buffer"))
            .unwrap();
        assert!(matches!(decision, Decision::Degraded(_)), "{decision:?}");
        let row = ctx
            .raw_boundary_artifacts
            .ownership_native
            .lines()
            .find(|row| row.starts_with("prepare::buffer#"))
            .unwrap();
        assert!(
            row.contains("\ttrue\tnot-selected\tCandidateNotSelected\t"),
            "{row}"
        );
        let receipt = ctx
            .raw_boundary_artifacts
            .additive_family_receipts
            .iter()
            .find(|r| r.family == "Ownership" && r.owner_path == "prepare")
            .expect("ownership-stage receipt");
        assert_eq!(
            receipt.cause,
            "unwitnessed-family-refusal:blocked-subject:copy-source-coupled"
        );
        // The composition itself held: no glue collided at the lent alias
        // argument, and the callee's interface took its dependency on the
        // owner's class (which is what falls with that class).
        let callee = ctx
            .raw_boundary_artifacts
            .additive_family_receipts
            .iter()
            .find(|r| r.family == "Ownership" && r.owner_path == "read")
            .expect("callee ownership-stage receipt");
        assert!(
            callee.cause.starts_with("new-family-dependency:"),
            "{}",
            callee.cause
        );
    })
    .unwrap();
}

#[test]
fn r407_view_alias_start_must_be_pure() {
    // The view's start is evaluated once at the binding; an effectful start
    // (`next()`) or one reading through the owner (`*buffer`) is not a
    // runtime-checked view of the owner and holds it.
    for start in ["next() as isize", "*buffer as isize"] {
        let input = format!(
            "{} static mut COUNTER: usize = 0; unsafe fn next()->usize {{ COUNTER+=1; COUNTER }} pub unsafe fn prepare()->u32 {{ let mut buffer=calloc(8,core::mem::size_of::<u32>()) as *mut u32; let mut row=buffer.offset({start}); *row.offset(1)=9; let value=*row.offset(1); free(buffer as *mut core::ffi::c_void); value }}",
            declarations()
        );
        ::utils::compilation::run_compiler_on_str(&input, |tcx| {
            let (table, _ctx) = super::decide_table_with_ctx_config(
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
            assert!(matches!(d, Decision::Degraded(_)), "{start}: {d:?}");
        })
        .unwrap();
    }
    // Control: a pure start delivers the view.
    let input = format!(
        "{} pub unsafe fn prepare(k: isize)->u32 {{ let mut buffer=calloc(8,core::mem::size_of::<u32>()) as *mut u32; let mut row=buffer.offset(k * 2); *row.offset(1)=9; let value=*row.offset(1); free(buffer as *mut core::ffi::c_void); value }}",
        declarations()
    );
    let s = verify(&input, "buffer", BoxShape::Slice, false);
    assert!(
        s.contains("let mut row: &mut [u32]=&mut (*(buffer))[(k * 2) as usize..];"),
        "{s}"
    );
    assert!(s.contains("row[1]=9;"), "{s}");
}

#[test]
fn r407_real_horizon_scan_hull_buffer_struct_view_alias() {
    // The verbatim corpus `horizon_scan` tail (`hull_buffer#242`): a
    // `malloc(sizeof(kmVec3) * pathlen * nsweeps)` owner of `kmVec3` values
    // (repr(C), rule E's zero), one per-sweep alias
    // `convex_hull = hull_buffer.offset(sweep * pathlen)` written and read
    // as `*convex_hull.offset(k)` (struct values by copy, some as arguments
    // of local callees), freed at the end. The function's raw parameters
    // and the other raw locals are the class siblings.
    let input = format!(
        r#"{}
extern "C" {{ fn __assert_fail(a: *const libc::c_char, f: *const libc::c_char, l: libc::c_uint, fun: *const libc::c_char) -> !; fn heman_image_texel(img: *mut heman_image, x: libc::c_int, y: libc::c_int) -> *mut libc::c_float; }}
#[repr(C)] #[derive(Copy, Clone)] pub struct heman_image_s {{ pub width: libc::c_int, pub height: libc::c_int, pub nbands: libc::c_int, pub data: *mut libc::c_float }}
pub type heman_image = heman_image_s;
#[derive(Copy, Clone)] #[repr(C)] pub struct kmVec3 {{ pub x: libc::c_float, pub y: libc::c_float, pub z: libc::c_float }}
static mut _occlusion_scale: libc::c_float = 1.0f32;
unsafe extern "C" fn azimuth_slope(mut a: kmVec3, mut b: kmVec3) -> libc::c_float {{ (b.z - a.z) / ((b.x - a.x) * (b.x - a.x) + (b.y - a.y) * (b.y - a.y)) }}
unsafe extern "C" fn compute_occlusion(mut thispt: kmVec3, mut horizonpt: kmVec3) -> libc::c_float {{ horizonpt.z - thispt.z }}
{}"#,
        c_declarations().replace("pub mod libc { pub use core::ffi::c_int;", "pub mod libc { pub use core::ffi::c_char; pub use core::ffi::c_uint; pub use core::ffi::c_int;"),
        HORIZON_SCAN_BODY
    );
    let s = verify(&input, "hull_buffer", BoxShape::Slice, false);
    assert!(
        s.contains("let mut hull_buffer: ::std::boxed::Box<[crate::kmVec3]> = ::std::vec![crate::kmVec3 { x: 0.0f32, y: 0.0f32, z: 0.0f32 };"),
        "{s}"
    );
    assert!(
        s.contains("let mut convex_hull: &mut [crate::kmVec3] = &mut (*(hull_buffer))[((sweep * pathlen) as isize) as usize..];"),
        "{s}"
    );
    assert!(
        s.contains("convex_hull[(0 as libc::c_int) as usize] = thispt;"),
        "{s}"
    );
    assert!(
        s.contains("horizonpt = convex_hull[(fresh4) as usize];"),
        "{s}"
    );
    assert!(s.contains("::std::mem::drop(hull_buffer);"), "{s}");
}

const HORIZON_SCAN_BODY: &str = r#"unsafe extern "C" fn horizon_scan(mut heightmap: *mut heman_image, mut result: *mut heman_image, mut startpts: *mut libc::c_int, mut nsweeps: libc::c_int, mut pathlen: libc::c_int, mut dx: libc::c_int, mut dy: libc::c_int) {
    let mut w = (*heightmap).width;
    let mut h = (*heightmap).height;
    let mut cellw = _occlusion_scale / (if w > h { w } else { h }) as libc::c_float;
    let mut cellh = _occlusion_scale / (if w > h { w } else { h }) as libc::c_float;
    let mut hull_buffer = malloc(
        (::std::mem::size_of::<kmVec3>() as libc::c_ulong)
            .wrapping_mul(pathlen as libc::c_ulong)
            .wrapping_mul(nsweeps as libc::c_ulong),
    ) as *mut kmVec3;
    let mut sweep: libc::c_int = 0;
    sweep = 0 as libc::c_int;
    while sweep < nsweeps {
        let mut convex_hull = hull_buffer.offset((sweep * pathlen) as isize);
        let mut p_0 = startpts.offset((sweep * 2 as libc::c_int) as isize);
        let mut i_0 = *p_0.offset(0 as libc::c_int as isize);
        let mut j_0 = *p_0.offset(1 as libc::c_int as isize);
        let mut thispt = kmVec3 { x: 0., y: 0., z: 0. };
        let mut horizonpt = kmVec3 { x: 0., y: 0., z: 0. };
        thispt.x = i_0 as libc::c_float * cellw;
        thispt.y = j_0 as libc::c_float * cellh;
        thispt
            .z = *heman_image_texel(
            heightmap,
            if 0 as libc::c_int
                > (if w - 1 as libc::c_int > i_0 { i_0 } else { w - 1 as libc::c_int })
            {
                0 as libc::c_int
            } else if w - 1 as libc::c_int > i_0 {
                i_0
            } else {
                w - 1 as libc::c_int
            },
            if 0 as libc::c_int
                > (if h - 1 as libc::c_int > j_0 { j_0 } else { h - 1 as libc::c_int })
            {
                0 as libc::c_int
            } else if h - 1 as libc::c_int > j_0 {
                j_0
            } else {
                h - 1 as libc::c_int
            },
        );
        let mut stack_top = 0 as libc::c_int;
        *convex_hull.offset(0 as libc::c_int as isize) = thispt;
        i_0 += dx;
        j_0 += dy;
        while i_0 >= 0 as libc::c_int && i_0 < w && j_0 >= 0 as libc::c_int && j_0 < h {
            thispt.x = i_0 as libc::c_float * cellw;
            thispt.y = j_0 as libc::c_float * cellh;
            thispt.z = *heman_image_texel(heightmap, i_0, j_0);
            while stack_top > 0 as libc::c_int {
                let mut s1 = azimuth_slope(
                    thispt,
                    *convex_hull.offset(stack_top as isize),
                );
                let mut s2 = azimuth_slope(
                    thispt,
                    *convex_hull.offset((stack_top - 1 as libc::c_int) as isize),
                );
                if s1 >= s2 {
                    break;
                }
                stack_top -= 1;
            }
            let fresh4 = stack_top;
            stack_top = stack_top + 1;
            horizonpt = *convex_hull.offset(fresh4 as isize);
            if stack_top < pathlen {} else {
                __assert_fail(
                    b"stack_top < pathlen\0" as *const u8 as *const libc::c_char,
                    b"../src/lighting.c\0" as *const u8 as *const libc::c_char,
                    213 as libc::c_int as libc::c_uint,
                    (*::std::mem::transmute::<
                        &[u8; 65],
                        &[libc::c_char; 65],
                    >(
                        b"void horizon_scan(heman_image *, heman_image *, int *, int, int)\0",
                    ))
                        .as_ptr(),
                );
            }
            *convex_hull.offset(stack_top as isize) = thispt;
            let mut occlusion = compute_occlusion(thispt, horizonpt);
            *heman_image_texel(result, i_0, j_0) += 1.0f32 / 16.0f32 * occlusion;
            i_0 += dx;
            j_0 += dy;
        }
        sweep += 1;
    }
    free(hull_buffer as *mut libc::c_void);
}"#;

const TRANSFORM_TO_DISTANCE_BODY: &str = r#"unsafe extern "C" fn transform_to_distance(mut sdf:
        *mut heman_image) {
    let mut width = (*sdf).width;
    let mut height = (*sdf).height;
    let mut size = width * height;
    let mut ff =
        calloc(size as libc::c_ulong,
                ::std::mem::size_of::<libc::c_float>() as libc::c_ulong) as
            *mut libc::c_float;
    let mut dd =
        calloc(size as libc::c_ulong,
                ::std::mem::size_of::<libc::c_float>() as libc::c_ulong) as
            *mut libc::c_float;
    let mut zz =
        calloc(((height + 1 as libc::c_int) *
                            (width + 1 as libc::c_int)) as libc::c_ulong,
                ::std::mem::size_of::<libc::c_float>() as libc::c_ulong) as
            *mut libc::c_float;
    let mut ww =
        calloc(size as libc::c_ulong,
                ::std::mem::size_of::<uint16_t>() as libc::c_ulong) as
            *mut uint16_t;
    let mut x: libc::c_int = 0;
    x = 0 as libc::c_int;
    while x < width {
        let mut f = ff.offset((height * x) as isize);
        let mut d = dd.offset((height * x) as isize);
        let mut z =
            zz.offset(((height + 1 as libc::c_int) * x) as isize);
        let mut w = ww.offset((height * x) as isize);
        let mut y = 0 as libc::c_int;
        while y < height {
            *f.offset(y as isize) =
                *((*sdf).data).offset(((y * width) as isize) +
                            (x as isize));
            y += 1;
        }
        edt(f, d, z, w, height);
        let mut y_0 = 0 as libc::c_int;
        while y_0 < height {
            *((*sdf).data).offset(((y_0 * width) as isize) +
                            (x as isize)) = *d.offset(y_0 as isize);
            y_0 += 1;
        }
        x += 1;
    }
    let mut y_1: libc::c_int = 0;
    y_1 = 0 as libc::c_int;
    while y_1 < height {
        let mut f_0 = ff.offset((width * y_1) as isize);
        let mut d_0 = dd.offset((width * y_1) as isize);
        let mut z_0 =
            zz.offset(((width + 1 as libc::c_int) * y_1) as isize);
        let mut w_0 = ww.offset((width * y_1) as isize);
        let mut x_0 = 0 as libc::c_int;
        while x_0 < width {
            *f_0.offset(x_0 as isize) =
                *((*sdf).data).offset(((y_1 * width) as isize) +
                            (x_0 as isize));
            x_0 += 1;
        }
        edt(f_0, d_0, z_0, w_0, width);
        let mut x_1 = 0 as libc::c_int;
        while x_1 < width {
            *((*sdf).data).offset(((y_1 * width) as isize) +
                            (x_1 as isize)) = *d_0.offset(x_1 as isize);
            x_1 += 1;
        }
        y_1 += 1;
    }
    free(ff as *mut libc::c_void);
    free(dd as *mut libc::c_void);
    free(zz as *mut libc::c_void);
    free(ww as *mut libc::c_void);
}
unsafe extern "C" fn edt(mut f: *mut libc::c_float,
    mut d: *mut libc::c_float, mut z: *mut libc::c_float,
    mut w: *mut uint16_t, mut n: libc::c_int) {
    let mut k = 0 as libc::c_int;
    let mut s: libc::c_float = 0.;
    *w.offset(0 as libc::c_int as isize) =
        0 as libc::c_int as uint16_t;
    *z.offset(0 as libc::c_int as isize) = -INF;
    *z.offset(1 as libc::c_int as isize) = INF;
    let mut q = 1 as libc::c_int;
    while q < n {
        s =
            (*f.offset(q as isize) + (q * q) as libc::c_float -
                        (*f.offset(*w.offset(k as isize) as isize) +
                                (*w.offset(k as isize) as libc::c_int *
                                            *w.offset(k as isize) as libc::c_int) as libc::c_float)) /
                (2 as libc::c_int * q -
                            2 as libc::c_int * *w.offset(k as isize) as libc::c_int) as
                    libc::c_float;
        while s <= *z.offset(k as isize) {
            k -= 1;
            s =
                (*f.offset(q as isize) + (q * q) as libc::c_float -
                            (*f.offset(*w.offset(k as isize) as isize) +
                                    (*w.offset(k as isize) as libc::c_int *
                                                *w.offset(k as isize) as libc::c_int) as libc::c_float)) /
                    (2 as libc::c_int * q -
                                2 as libc::c_int * *w.offset(k as isize) as libc::c_int) as
                        libc::c_float;
        }
        k += 1;
        *w.offset(k as isize) = q as uint16_t;
        *z.offset(k as isize) = s;
        *z.offset((k + 1 as libc::c_int) as isize) = INF;
        q += 1;
    }
    k = 0 as libc::c_int;
    let mut q_0 = 0 as libc::c_int;
    while q_0 < n {
        while *z.offset((k + 1 as libc::c_int) as isize) <
                q_0 as libc::c_float {
            k += 1;
        }
        *d.offset(q_0 as isize) =
            ((q_0 - *w.offset(k as isize) as libc::c_int) *
                            (q_0 - *w.offset(k as isize) as libc::c_int)) as
                    libc::c_float + *f.offset(*w.offset(k as isize) as isize);
        q_0 += 1;
    }
}"#;

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
fn r395_scalar_arithmetic_call_arguments_are_pure_but_effectful_ones_hold() {
    // heman `qselect(vals, npixels, tier * npixels / nsteps)`.
    let input = format!(
        "{} unsafe fn read(p:*mut u32, k:usize)->u32 {{ *p.offset(k as isize) }} pub unsafe fn prepare(n:usize)->u32 {{ let mut buffer=calloc(4,core::mem::size_of::<u32>()) as *mut u32; *buffer=9; let value=read(buffer, (n * 2 + 1) / 3 % 4); free(buffer as *mut core::ffi::c_void); value }}",
        declarations()
    );
    let s = verify(&input, "buffer", BoxShape::Slice, false);
    assert!(s.contains("read(<[_]>::as_mut_ptr(&mut *(buffer)), (n * 2 + 1) / 3 % 4)"));
    let effectful = format!(
        "{} static mut COUNTER: usize = 0; unsafe fn next()->usize {{ COUNTER+=1; COUNTER }} unsafe fn read(p:*mut u32, k:usize)->u32 {{ *p.offset(k as isize) }} pub unsafe fn prepare()->u32 {{ let mut buffer=calloc(4,core::mem::size_of::<u32>()) as *mut u32; *buffer=9; let value=read(buffer, next() * 2); free(buffer as *mut core::ffi::c_void); value }}",
        declarations()
    );
    ::utils::compilation::run_compiler_on_str(&effectful, |tcx| {
        let (table, _ctx) = super::decide_table_with_ctx_config(
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
        assert!(matches!(d, Decision::Degraded(_)), "{d:?}");
    })
    .unwrap();
}

#[test]
fn r408_argument_reading_through_the_owner_holds_no_hoist_is_owed() {
    // E5C-3 (relay 022 §2): a lend/transfer argument list may not carry a
    // read the borrow/move invalidates. The scalar-argument permit admits
    // only literals, scalar locals, casts and arithmetic over them, so an
    // argument reading THROUGH the owner (`read(buffer, *buffer.offset(1))`)
    // or through a view of it (`read(buffer, *row)`) holds the owner — no
    // read is hoisted. Each case pairs with a delivering control whose only
    // difference is the argument.
    let fixture = |prefix: &str, argument: &str| {
        format!(
            "{} unsafe fn read(p:*mut u32, k:usize)->u32 {{ *p.offset(k as isize) }} pub unsafe fn prepare()->u32 {{ let mut buffer=calloc(4,core::mem::size_of::<u32>()) as *mut u32; {prefix} let value=read(buffer, {argument}); free(buffer as *mut core::ffi::c_void); value }}",
            declarations()
        )
    };
    for (prefix, argument) in [
        ("*buffer=1;", "*buffer.offset(1) as usize"),
        (
            "let mut row=buffer.offset(1); *row.offset(0)=2;",
            "*row.offset(0) as usize",
        ),
    ] {
        ::utils::compilation::run_compiler_on_str(&fixture(prefix, argument), |tcx| {
            let (table, _ctx) = super::decide_table_with_ctx_config(
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
            assert!(matches!(d, Decision::Degraded(_)), "{argument}: {d:?}");
        })
        .unwrap();
        let s = verify(&fixture(prefix, "1"), "buffer", BoxShape::Slice, false);
        assert!(
            s.contains("read(<[_]>::as_mut_ptr(&mut *(buffer)), 1)"),
            "{s}"
        );
    }
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
