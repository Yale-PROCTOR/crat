//! R395 body-local fixtures. Raw inputs are compiled/analyzed, never executed.
use super::decision::{Decision, box_facts::BoxShape};

fn declarations() -> &'static str {
    r#"extern "C" { fn malloc(n:usize)->*mut core::ffi::c_void; fn calloc(n:usize,s:usize)->*mut core::ffi::c_void; fn free(p:*mut core::ffi::c_void); }"#
}

/// R423: `name` is a local the table decides for another family (a slice or
/// cursor over the alias's own accesses) — then the owner's view-alias plan
/// holds typed and this witness's delivering branch does not apply.
fn alias_is_another_family(input: &str, name: &str) -> bool {
    ::utils::compilation::run_compiler_on_str(input, |tcx| {
        let (table, _ctx) = super::decide_table_with_ctx_config(
            tcx,
            Some((
                super::A5Mode::PreciseReplay,
                Some(super::WholeProgramAttestation::FrozenBenchmarkGraph),
            )),
        )
        .unwrap();
        table.entries.iter().any(|(subject, decision)| {
            subject.param_name.as_deref() == Some(name)
                && !matches!(decision, Decision::Degraded(_))
        })
    })
    .unwrap()
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
        // R412-2: every expression edit must round-trip through the AST
        // emission's graft parser (the pretty printer's spelling, e.g. the
        // trailing comma of a struct literal); a refused graft leaves the
        // source node intact and the program does not compile.
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
fn r419_annotated_binding_is_retyped_on_both_emission_paths() {
    // bzip2 spells its owners `let mut v: *mut T = malloc(..)`; tulip's
    // `ti_buffer_new::ret` is the same shape under wave-6a's plan. The
    // declaration channel replaces the source's annotation with the Box type
    // on the text path and on the census (AST) path, so the declaration
    // inventory has the row the ledger counts (R419-1/3).
    let input = format!(
        "{} pub unsafe fn prepare(n: usize) -> u32 {{ let mut buffer: *mut u32 = calloc(4, core::mem::size_of::<u32>()) as *mut u32; *buffer.offset(1) = 9; let value = *buffer.offset(1); free(buffer as *mut core::ffi::c_void); value }}",
        declarations()
    );
    let s = verify(&input, "buffer", BoxShape::Slice, false);
    assert!(
        s.contains(
            "let mut buffer: ::std::boxed::Box<[u32]> = ::std::vec![0u32; 4].into_boxed_slice();"
        ),
        "{s}"
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
        reverted_count,
        first_diags,
        ..
    } = outcome
    else {
        panic!("{outcome:?}")
    };
    assert_eq!((reverted_count, first_diags.len()), (0, 0), "{source}");
    let flat: String = source.split_whitespace().collect::<Vec<_>>().join(" ");
    assert!(
        flat.contains("let mut buffer: ::std::boxed::Box<[u32]> ="),
        "{source}"
    );
    let rows =
        super::delivery_custody::inventory_source("fixture.rs", &source).expect("custody parse");
    let row = rows
        .iter()
        .find(|row| row.owner == "prepare" && row.binding == "buffer")
        .unwrap_or_else(|| panic!("{rows:#?}"));
    assert!(row.type_is_fully_explicit, "{row:#?}");
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
    // that class — and which side of it this frame is on is the frame's own
    // answer (R217-2(a), restated at relay 045). On a base where no family
    // takes the aliases they stay `Degraded(copy-source-coupled)` siblings
    // with a c-arm requirement, which holds the whole owner class
    // (`blocked-subject:copy-source-coupled`, `missing-required-arm:c`) — the
    // R407-12 frontier. On a composition carrying wave-5d2's rule B and R442
    // the aliases are decided slices over a DELIVERED owner (their report
    // 023), and the same four owners read `selected` / `Box`. Pinned on both:
    // no interval collision, every bundle derived, `edt`'s dependency taken,
    // and the four owners agreeing on one frame.
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
        let mut delivered = 0;
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
            // The native bundle exists on every frame — the alias permit
            // admitted every use — and which way it then goes is the frame's:
            // R217-2(a), restated at relay 045 for the composition wave-5d2's
            // rule B and R442 make (their report 023).
            let row = ctx
                .raw_boundary_artifacts
                .ownership_native
                .lines()
                .find(|row| row.starts_with(&format!("transform_to_distance::{name}#")))
                .unwrap_or_else(|| panic!("{name}: no native audit row"));
            assert!(row.contains("\ttrue\t"), "{name}: considered: {row}");
            if row.contains("\tselected\t") {
                // The composed reading: the aliases are a deciding family's to
                // render, R442 keeps the owner typed, and the owner delivers.
                assert!(
                    matches!(decision, Decision::Box(_)),
                    "{name}: selected but not delivered: {decision:?}"
                );
                delivered += 1;
            } else {
                // This base's reading: no family takes the aliases, they stay
                // `Degraded(copy-source-coupled)` siblings, and the class hold
                // withdraws the owner with them (the R407-12 frontier).
                assert!(
                    row.contains("\tnot-selected\tCandidateNotSelected\t"),
                    "{name}: {row}"
                );
                assert!(
                    matches!(decision, Decision::Degraded(_)),
                    "{name}: {decision:?}"
                );
            }
        }
        assert!(
            delivered == 0 || delivered == 4,
            "the four owners share one frame, {delivered} delivered"
        );
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
        // The callee's interface takes a dependency on the owner's class. The
        // cause text carries a re-derivation anchor on a composition
        // (`exclusion-rederivation:anchor=…:new-family-dependency:…`), so the
        // pin is the dependency itself, not the prefix.
        assert!(
            ownership_receipts
                .iter()
                .any(|cause| cause.starts_with("edt: ") && cause.contains("new-family-dependency")),
            "{ownership_receipts:?}"
        );
        assert!(
            delivered == 4
                || ownership_receipts
                    .iter()
                    .any(|cause| cause.starts_with("transform_to_distance: ")),
            "held here, so the owner class must say so: {ownership_receipts:?}"
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
        let row = ctx
            .raw_boundary_artifacts
            .ownership_native
            .lines()
            .find(|row| row.starts_with("prepare::buffer#"))
            .unwrap();
        // Three admissible readings (R217-2(a), R423): the owner is held by
        // its class on this base; on a composition that releases the sibling
        // hold it DELIVERS; where another family decides the alias, the
        // owner holds typed and that family owns the alias's uses.
        match decision {
            Decision::Box(plan) => {
                assert_eq!(plan.shape, BoxShape::Slice);
                assert!(row.contains("\tbox\ttrue\tselected\t"), "{row}");
                return;
            }
            Decision::Degraded(_) => {}
            other => panic!("{other:?}"),
        }
        if row.contains("native-view-alias-family-owned") {
            return;
        }
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
        assert!(
            receipt.cause == "unwitnessed-family-refusal:blocked-subject:copy-source-coupled"
                || receipt.cause.starts_with("exclusion-rederivation:"),
            "{}",
            receipt.cause
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
    // Unless another family decides the alias on this head (R423), where the
    // owner holds typed and that family owns the alias's uses.
    if alias_is_another_family(&input, "row") {
        return;
    }
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
        s.contains("let mut hull_buffer: ::std::boxed::Box<[crate::kmVec3]> = ::std::vec![crate::kmVec3 { x: 0.0f32, y: 0.0f32, z: 0.0f32, };"),
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
        let control = fixture(prefix, "1");
        if alias_is_another_family(&control, "row") {
            continue;
        }
        let s = verify(&control, "buffer", BoxShape::Slice, false);
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

/// R431, the native half: a local MOVED OUT of another object's field is an
/// owner only once a field transaction owns that field. Here the model DOES
/// grant the moved-out local `Owning` (`b`, freed in the same body), and the
/// native stage still holds it fail-closed — typing `b` a `Box<[u8]>` while
/// `(*h).buf` stays raw would leave the container's copy pointing into memory
/// this Box closes. The holder's own allocation (`h`) delivers beside it, so
/// the hold is the field-load rule's and nothing else's.
#[test]
fn r431_a_moved_out_field_owner_holds_until_a_field_transaction_owns_the_field() {
    let input = r#"#![allow(dead_code, unused_mut, unused_unsafe, unused_assignments, unused_variables, non_camel_case_types, non_snake_case)]
extern "C" { fn malloc(_: u64) -> *mut std::ffi::c_void; fn free(_: *mut std::ffi::c_void); }
#[repr(C)] pub struct Holder { pub buf: *mut u8, pub len: i32 }
pub unsafe extern "C" fn run() {
    let mut h = malloc(::std::mem::size_of::<Holder>() as u64) as *mut Holder;
    (*h).buf = malloc(64 as u64) as *mut u8;
    (*h).len = 64 as i32;
    let mut b = (*h).buf;
    (*h).buf = 0 as *mut u8;
    free(b as *mut std::ffi::c_void);
    free(h as *mut std::ffi::c_void);
}
"#;
    let joined = ::utils::compilation::run_compiler_on_str(input, |tcx| {
        let (_, ctx) = super::decide_table_with_ctx_config(
            tcx,
            Some((
                super::A5Mode::PreciseReplay,
                Some(super::WholeProgramAttestation::FrozenBenchmarkGraph),
            )),
        )
        .unwrap();
        let audit = &ctx.raw_boundary_artifacts.ownership_native;
        println!("R431_NATIVE\n{audit}");
        let row = |subject: &str| {
            audit
                .lines()
                .find(|line| line.starts_with(subject))
                .unwrap_or_else(|| panic!("{subject}: {audit}"))
                .to_owned()
        };
        let moved_out = row("run::b#");
        assert!(
            moved_out.contains("\towning\t") && moved_out.contains("\ttrue\t"),
            "the model grants it and the native stage considers it: {moved_out}"
        );
        // R453-1 / R217-2(a): which reading holds is the FRAME's answer. Where
        // no field family answers the seam — this line's stub body — the owner
        // holds fail-closed; where a composition's join is live and a
        // transaction owns `Holder.buf` (wave-6f's `opt-box`), the same row is
        // SELECTED and the local takes that transaction's shape (R440-4).
        // Nothing else is accepted.
        assert!(
            (moved_out.contains("held") && moved_out.contains("native-field-load-field-not-owned"))
                || moved_out.contains("\tselected\t"),
            "{moved_out}"
        );
        assert!(
            row("run::h#").contains("selected"),
            "the holder still delivers"
        );
        moved_out.contains("\tselected\t")
    })
    .unwrap();
    // End to end: `b` keeps its raw form and its C free, `h` delivers with
    // its drop at the C free site — no second owner of the same allocation.
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
    if joined {
        // MEASURED on `batch-12-dry14` `2e0a2a1e3`: the field transaction is
        // `Holder.buf = opt-box (applied)` and this producer selects both
        // locals, so the declaration takes the transaction's shape — but the
        // moved-out LOAD that initializes `b` is still spelled raw, so the
        // candidate is ill-typed (`E0308` at the initializer: expected
        // `Option<Box<u8>>`, found `*mut u8`) and the program falls back
        // UNMODIFIED. That fallback is the fail-closed behaviour this arm
        // pins: nothing ill-typed and no second owner escapes. It is a
        // TRIPWIRE, not an endorsement — the day the load is rendered this
        // goes red and the arm tightens to the two-drop delivery above.
        let super::RewriteOutcome::Degraded { reason, source, .. } = outcome else {
            panic!("the load renders now — tighten this arm: {outcome:?}")
        };
        assert!(source.contains("let mut b = (*h).buf;"), "{source}");
        // Two joined readings, both measured on `batch-12-dry14` `2e0a2a1e3`
        // and both fail-closed (the program is returned unmodified):
        //   * without R455-6(b): the field family's applied transaction does
        //     not reach the emitted tree — the struct field stays `*mut u8`
        //     and the load stays bare — while this producer's declaration
        //     type lands, so verify reports the `E0308` and recovery finds no
        //     compiling subset;
        //   * with R455-6(b): this producer's `take()` claims the load's span
        //     first and the field family's own `owned-field-move` wrap for the
        //     same span is refused, so round-0 emit stops there.
        // Neither is a delivery, and the panic above is what fires the day one
        // becomes one.
        assert!(
            reason.contains("recovery-degraded") || reason.contains("wrap-claim-refused"),
            "{reason}"
        );
        return;
    }
    let super::RewriteOutcome::Emitted { source, .. } = outcome else { panic!("{outcome:?}") };
    println!("R431_EMITTED_BEGIN\n{source}\nR431_EMITTED_END joined={joined}");
    assert!(source.contains("let mut b = (*h).buf;"), "{source}");
    assert!(
        source.contains("free(b as *mut std::ffi::c_void)")
            || source.contains("free(b as *mut ::std::ffi::c_void)"),
        "{source}"
    );
    assert_eq!(source.matches("::std::mem::drop(").count(), 1, "{source}");
}

/// heman's `heman_points_from_poisson`, as the derived substrate spells it
/// (`benchmarks/rs-crown-derived/heman/lib.rs`): two `malloc`ed `c_int`
/// buffers indexed throughout and freed at the end, in a body that also takes
/// `&mut seed`, `&mut rvec`, `&mut delta` and `&mut *samples.offset(i)` — the
/// last one a reference into ANOTHER allocation.
fn poisson_fixture() -> &'static str {
    r#"#![allow(dead_code, unused_mut, unused_unsafe, unused_assignments, unused_variables, non_camel_case_types, non_snake_case)]
pub mod libc {
    pub use core::ffi::c_double;
    pub use core::ffi::c_float;
    pub use core::ffi::c_int;
    pub use core::ffi::c_uint;
    pub use core::ffi::c_ulong;
    pub use core::ffi::c_void;
}
extern "C" {
    fn malloc(n: libc::c_ulong) -> *mut libc::c_void;
    fn free(p: *mut libc::c_void);
    fn sqrtf(x: libc::c_float) -> libc::c_float;
    fn ceil(x: libc::c_double) -> libc::c_double;
}
#[repr(C, packed)]
#[derive(Copy, Clone)]
pub struct kmVec2 { pub x: libc::c_float, pub y: libc::c_float }
#[repr(C)]
#[derive(Copy, Clone)]
pub struct heman_image_s {
    pub width: libc::c_int,
    pub height: libc::c_int,
    pub nbands: libc::c_int,
    pub data: *mut libc::c_float,
}
pub type heman_image = heman_image_s;
pub type heman_points = heman_image_s;
pub unsafe extern "C" fn heman_image_create(w: libc::c_int, h: libc::c_int, n: libc::c_int) -> *mut heman_image {
    let mut img = malloc(::std::mem::size_of::<heman_image_s>() as libc::c_ulong) as *mut heman_image_s;
    (*img).width = w;
    (*img).height = h;
    (*img).nbands = n;
    (*img).data = malloc(((w * h * n) as libc::c_ulong).wrapping_mul(::std::mem::size_of::<libc::c_float>() as libc::c_ulong)) as *mut libc::c_float;
    return img;
}
pub unsafe extern "C" fn randhash(seed: libc::c_uint) -> libc::c_uint {
    return seed.wrapping_mul(1103515245 as libc::c_uint).wrapping_add(12345 as libc::c_uint);
}
pub unsafe extern "C" fn randhashf(seed: libc::c_uint, a: libc::c_float, b: libc::c_float) -> libc::c_float {
    return a + (b - a) * (randhash(seed) as libc::c_float / 4294967295.0f32);
}
pub unsafe extern "C" fn sample_annulus(radius: libc::c_float, center: kmVec2, seed: *mut libc::c_uint) -> kmVec2 {
    let mut r = kmVec2 { x: 0., y: 0. };
    r.x = center.x + radius * randhash(*seed) as libc::c_float;
    *seed = (*seed).wrapping_add(1);
    r.y = center.y + radius * randhash(*seed) as libc::c_float;
    return r;
}
pub unsafe extern "C" fn kmVec2Add(d: *mut kmVec2, a: *mut kmVec2, b: *mut kmVec2) -> *mut kmVec2 {
    (*d).x = (*a).x + (*b).x;
    (*d).y = (*a).y + (*b).y;
    return d;
}
pub unsafe extern "C" fn kmVec2Subtract(d: *mut kmVec2, a: *mut kmVec2, b: *mut kmVec2) -> *mut kmVec2 {
    (*d).x = (*a).x - (*b).x;
    (*d).y = (*a).y - (*b).y;
    return d;
}
pub unsafe extern "C" fn kmVec2Scale(d: *mut kmVec2, a: *mut kmVec2, s: libc::c_float) -> *mut kmVec2 {
    (*d).x = (*a).x * s;
    (*d).y = (*a).y * s;
    return d;
}
pub unsafe extern "C" fn kmVec2LengthSq(a: *mut kmVec2) -> libc::c_float {
    return (*a).x * (*a).x + (*a).y * (*a).y;
}
pub unsafe extern "C" fn heman_points_from_poisson(mut width:
        libc::c_float, mut height: libc::c_float,
    mut radius: libc::c_float) -> *mut heman_points {
    let mut maxattempts = 30 as libc::c_int;
    let mut rscale =
        1.0f32 /
            (2147483647 as libc::c_int as
                                libc::c_uint).wrapping_mul(2 as
                            libc::c_uint).wrapping_add(1 as libc::c_uint) as
                libc::c_float;
    let mut seed = 0 as libc::c_int as libc::c_uint;
    let mut rvec = kmVec2 { x: 0., y: 0. };
    rvec.y = radius;
    rvec.x = rvec.y;
    let mut r2 = radius * radius;
    let mut cellsize =
        radius / sqrtf(2 as libc::c_int as libc::c_float);
    let mut invcell = 1.0f32 / cellsize;
    let mut ncols =
        ceil((width * invcell) as libc::c_double) as libc::c_int;
    let mut nrows =
        ceil((height * invcell) as libc::c_double) as libc::c_int;
    let mut maxcol = ncols - 1 as libc::c_int;
    let mut maxrow = nrows - 1 as libc::c_int;
    let mut ncells = ncols * nrows;
    let mut grid =
        malloc((ncells as
                            libc::c_ulong).wrapping_mul(::std::mem::size_of::<libc::c_int>()
                        as libc::c_ulong)) as *mut libc::c_int;
    let mut i = 0 as libc::c_int;
    while i < ncells {
        *grid.offset(i as isize) = -(1 as libc::c_int);
        i += 1;
    }
    let mut actives =
        malloc((ncells as
                            libc::c_ulong).wrapping_mul(::std::mem::size_of::<libc::c_int>()
                        as libc::c_ulong)) as *mut libc::c_int;
    let mut nactives = 0 as libc::c_int;
    let mut result =
        heman_image_create(ncells, 1 as libc::c_int,
            2 as libc::c_int);
    let mut samples = (*result).data as *mut kmVec2;
    let mut nsamples = 0 as libc::c_int;
    let mut pt = kmVec2 { x: 0., y: 0. };
    let fresh5 = seed;
    seed = seed.wrapping_add(1);
    pt.x = width * randhash(fresh5) as libc::c_float * rscale;
    let fresh6 = seed;
    seed = seed.wrapping_add(1);
    pt.y = height * randhash(fresh6) as libc::c_float * rscale;
    let fresh7 = nactives;
    nactives = nactives + 1;
    *actives.offset(fresh7 as isize) = nsamples;
    *grid.offset(((pt.x * invcell) as libc::c_int +
                            ncols * (pt.y * invcell) as libc::c_int) as isize) =
        *actives.offset(fresh7 as isize);
    let fresh9 = nsamples;
    nsamples = nsamples + 1;
    *samples.offset(fresh9 as isize) = pt;
    while nsamples < ncells {
        let fresh10 = seed;
        seed = seed.wrapping_add(1);
        let mut aindex =
            (if randhashf(fresh10, 0 as libc::c_int as libc::c_float,
                                nactives as libc::c_float) >
                            (nactives - 1 as libc::c_int) as libc::c_float {
                        (nactives - 1 as libc::c_int) as libc::c_float
                    } else {
                        let fresh11 = seed;
                        seed = seed.wrapping_add(1);
                        randhashf(fresh11, 0 as libc::c_int as libc::c_float,
                            nactives as libc::c_float)
                    }) as libc::c_int;
        let mut sindex = *actives.offset(aindex as isize);
        let mut found = 0 as libc::c_int;
        let mut j = kmVec2 { x: 0., y: 0. };
        let mut minj = kmVec2 { x: 0., y: 0. };
        let mut maxj = kmVec2 { x: 0., y: 0. };
        let mut delta = kmVec2 { x: 0., y: 0. };
        let mut attempt: libc::c_int = 0;
        attempt = 0 as libc::c_int;
        while attempt < maxattempts && found == 0 {
            pt =
                sample_annulus(radius, *samples.offset(sindex as isize),
                    &mut seed);
            if !(pt.x < 0 as libc::c_int as libc::c_float ||
                                    pt.x >= width || pt.y < 0 as libc::c_int as libc::c_float ||
                            pt.y >= height) {
                maxj = pt;
                minj = maxj;
                kmVec2Add(&mut maxj, &mut maxj, &mut rvec);
                kmVec2Subtract(&mut minj, &mut minj, &mut rvec);
                kmVec2Scale(&mut minj, &mut minj, invcell);
                kmVec2Scale(&mut maxj, &mut maxj, invcell);
                minj.x =
                    (if 0 as libc::c_int >
                                    (if maxcol > minj.x as libc::c_int {
                                            minj.x as libc::c_int
                                        } else { maxcol }) {
                                0 as libc::c_int
                            } else if maxcol > minj.x as libc::c_int {
                                minj.x as libc::c_int
                            } else { maxcol }) as libc::c_float;
                maxj.x =
                    (if 0 as libc::c_int >
                                    (if maxcol > maxj.x as libc::c_int {
                                            maxj.x as libc::c_int
                                        } else { maxcol }) {
                                0 as libc::c_int
                            } else if maxcol > maxj.x as libc::c_int {
                                maxj.x as libc::c_int
                            } else { maxcol }) as libc::c_float;
                minj.y =
                    (if 0 as libc::c_int >
                                    (if maxrow > minj.y as libc::c_int {
                                            minj.y as libc::c_int
                                        } else { maxrow }) {
                                0 as libc::c_int
                            } else if maxrow > minj.y as libc::c_int {
                                minj.y as libc::c_int
                            } else { maxrow }) as libc::c_float;
                maxj.y =
                    (if 0 as libc::c_int >
                                    (if maxrow > maxj.y as libc::c_int {
                                            maxj.y as libc::c_int
                                        } else { maxrow }) {
                                0 as libc::c_int
                            } else if maxrow > maxj.y as libc::c_int {
                                maxj.y as libc::c_int
                            } else { maxrow }) as libc::c_float;
                let mut reject = 0 as libc::c_int;
                j.y = minj.y;
                while j.y <= maxj.y && reject == 0 {
                    j.x = minj.x;
                    while j.x <= maxj.x && reject == 0 {
                        let mut entry =
                            *grid.offset((j.y as libc::c_int * ncols +
                                                j.x as libc::c_int) as isize);
                        if entry > -(1 as libc::c_int) && entry != sindex {
                            kmVec2Subtract(&mut delta,
                                &mut *samples.offset(entry as isize), &mut pt);
                            if kmVec2LengthSq(&mut delta) < r2 {
                                reject = 1 as libc::c_int;
                            }
                        }
                        j.x += 1.;
                    }
                    j.y += 1.;
                }
                if !(reject != 0) { found = 1 as libc::c_int; }
            }
            attempt += 1;
        }
        if found != 0 {
            let fresh12 = nactives;
            nactives = nactives + 1;
            *actives.offset(fresh12 as isize) = nsamples;
            *grid.offset(((pt.x * invcell) as libc::c_int +
                                    ncols * (pt.y * invcell) as libc::c_int) as isize) =
                *actives.offset(fresh12 as isize);
            let fresh14 = nsamples;
            nsamples = nsamples + 1;
            *samples.offset(fresh14 as isize) = pt;
        } else {
            nactives -= 1;
            if nactives <= 0 as libc::c_int { break; }
            *actives.offset(aindex as isize) =
                *actives.offset(nactives as isize);
        }
    }
    (*result).width = nsamples;
    free(grid as *mut libc::c_void);
    free(actives as *mut libc::c_void);
    return result;
}
"#
}

/// R434 (relay 036 §4, the census-of-record `Source::UnsupportedOwnerUse`
/// rows): the permit refused EVERY owner of a body that takes ANY reference
/// anywhere. A reference can alias the owner only when it is ROOTED at the
/// owner or at one of its view aliases — every other use of the owner is
/// accounted by this same permit, so no other local of the body holds this
/// allocation's address. Both of heman's poisson owners now deliver
/// `Box<[i32]>`, every access becomes indexing, the reference into the other
/// allocation is left exactly as it was, and each C `free` becomes a drop
/// where it stood.
#[test]
fn r434_a_reference_that_cannot_reach_the_owner_keeps_the_owner() {
    // The permit and the decision are the rule's own claim, and hold on every
    // frame: both owners are admitted and decided Box.
    ::utils::compilation::run_compiler_on_str(poisson_fixture(), |tcx| {
        let (table, _) = super::decide_table_with_ctx_config(
            tcx,
            Some((
                super::A5Mode::PreciseReplay,
                Some(super::WholeProgramAttestation::FrozenBenchmarkGraph),
            )),
        )
        .unwrap();
        for owner in ["grid", "actives"] {
            let (_, decision) = table
                .entries
                .iter()
                .find(|(subject, _)| {
                    subject.param_name.as_deref() == Some(owner)
                        && tcx.def_path_str(subject.fn_did.to_def_id())
                            == "heman_points_from_poisson"
                })
                .unwrap_or_else(|| panic!("{owner}"));
            assert!(
                matches!(decision, Decision::Box(plan) if plan.shape == BoxShape::Slice),
                "{owner}: {decision:?}"
            );
        }
    })
    .unwrap();
    let outcome = super::rewrite_core_injected(
        ::utils::compilation::str_to_input(poisson_fixture()),
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
        degradations,
        ..
    } = outcome
    else {
        panic!("{outcome:?}")
    };
    println!("R434_EMITTED_BEGIN\n{source}\nR434_EMITTED_END reverted={reverted_count}");
    // R217-2(a), the composed reading (assembler `batch-10-dry2` `c97e6162e`):
    // the two owners are still planned and selected there, and the emitted
    // function is then REVERTED by the per-function verify gate — the revert is
    // the composition's, not this rule's, and the rows say so exactly.
    if reverted_count > 0 {
        for owner in ["grid#", "actives#"] {
            assert!(
                degradations.iter().any(|degraded| {
                    degraded.subject.contains(owner)
                        && degraded.reason.key() == "reverted-after-verify-failure"
                }),
                "{owner}: {:?}",
                degradations
                    .iter()
                    .map(|d| (d.subject.clone(), d.reason.key()))
                    .collect::<Vec<_>>()
            );
        }
        return;
    }
    let source = verify(poisson_fixture(), "grid", BoxShape::Slice, false);
    assert!(
        source.contains("grid[(i) as usize] = -(1 as libc::c_int)"),
        "{source}"
    );
    // The reference into the OTHER allocation is untouched, and so is the
    // scalar one the callee writes through.
    assert!(
        source.contains("&mut *samples.offset(entry as isize)"),
        "{source}"
    );
    assert!(source.contains("&mut seed"), "{source}");
    assert_eq!(source.matches("::std::mem::drop(").count(), 2, "{source}");
    let other = verify(poisson_fixture(), "actives", BoxShape::Slice, false);
    assert!(
        other.contains("actives[(aindex) as usize] = actives[(nactives) as usize]"),
        "{other}"
    );
}

/// The refusals R434 keeps: a reference rooted AT the owner, one rooted at a
/// view alias of the owner, a closure, and a reference VALUE this body did not
/// create (a call's `&T` result, whose provenance is unknown). The first two
/// shapes are ALSO uses of the owner, so on this base the use accounting
/// refuses them before R434's root test does (measured: disabling either root
/// clause leaves the refusal in place); the clause is the explicit statement
/// of the invariant and stays fail-closed for a shape the accounting does not
/// see.
#[test]
fn r434_a_reference_that_can_reach_the_owner_still_refuses() {
    let owner =
        "let mut buffer=malloc(4*core::mem::size_of::<i32>()) as *mut i32; *buffer.offset(1)=7;";
    for body in [
        // rooted at the owner
        "let mut r=&mut *buffer.offset(1); *r=9;",
        // rooted at a view alias of the owner
        "let mut view=buffer.offset(1); let mut r=&mut *view.offset(0); *r=9;",
        // a closure can capture anything
        "let f=||{}; f();",
        // a reference VALUE this body did not create
        "let r=borrowed(); let _=*r;",
    ] {
        let input = format!(
            "{} unsafe fn borrowed()->&'static i32 {{ &7 }} pub unsafe fn owner_body(){{ {owner} {body} free(buffer as *mut core::ffi::c_void); }}",
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
            let program = super::collect_program(tcx);
            let (subject, _) = table
                .entries
                .iter()
                .find(|(subject, _)| subject.param_name.as_deref() == Some("buffer"))
                .unwrap_or_else(|| panic!("{body}"));
            assert!(
                matches!(
                    super::decision::ownership_fields_source::derive(
                        &program,
                        subject,
                        &ctx.constructions
                    ),
                    Err(super::decision::ownership_fields_source::SourceHold::UnsupportedOwnerUse)
                ),
                "{body}"
            );
        })
        .unwrap();
    }
}

/// R435 (relay 037 STOP 1, granted): heman's `heman_points_from_density`
/// indexes one owner THROUGH another — `*grid.offset((gcapacity * gindex +
/// *ngrid.offset(gindex as isize)) as isize)`. Both accesses are this family's
/// edits and one contains the other, so the pair claimed a single interval and
/// the whole Ownership family was withdrawn
/// (`unwitnessed-family-refusal:intra-class-interval-overlap`). The outer edit
/// is now rendered OVER its re-rendered inner and the contained edit is
/// dropped: both owners deliver, and the emitted index reads
/// `grid[((4*i + ngrid[(i) as usize])) as usize]`.
#[test]
fn r435_an_owner_access_nested_in_another_owners_index_composes() {
    let input = format!(
        "{} pub unsafe fn density(){{ let mut grid=malloc(8*core::mem::size_of::<i32>()) as *mut i32; let mut ngrid=malloc(4*core::mem::size_of::<i32>()) as *mut i32; let mut i=0; while i<4 {{ *ngrid.offset(i as isize)=0; i+=1; }} *grid.offset((4*i + *ngrid.offset(i as isize)) as isize)=7; *ngrid.offset(i as isize)+=1; free(grid as *mut core::ffi::c_void); free(ngrid as *mut core::ffi::c_void); }}",
        declarations()
    );
    let source = verify(&input, "grid", BoxShape::Slice, false);
    assert!(
        source.contains("grid[((4*i + ngrid[(i) as usize])) as usize]=7"),
        "the outer access carries the rendered inner: {source}"
    );
    // The inner owner keeps every other access of its own.
    assert!(source.contains("ngrid[(i) as usize]=0"), "{source}");
    assert!(source.contains("ngrid[(i) as usize]+=1"), "{source}");
    let other = verify(&input, "ngrid", BoxShape::Slice, false);
    assert_eq!(other, source);
    // The composition is receipted on the outer plan, and the contained edit
    // is gone from the inner one.
    ::utils::compilation::run_compiler_on_str(&input, |tcx| {
        let (table, _) = super::decide_table_with_ctx_config(
            tcx,
            Some((
                super::A5Mode::PreciseReplay,
                Some(super::WholeProgramAttestation::FrozenBenchmarkGraph),
            )),
        )
        .unwrap();
        let plan_of = |name: &str| {
            let (_, decision) = table
                .entries
                .iter()
                .find(|(subject, _)| subject.param_name.as_deref() == Some(name))
                .unwrap_or_else(|| panic!("{name}"));
            let Decision::Box(plan) = decision else { panic!("{name}: {decision:?}") };
            plan.clone()
        };
        let outer = plan_of("grid");
        let composed: Vec<_> = outer
            .receipts
            .iter()
            .filter(|receipt| receipt.starts_with("native-box-access-composed"))
            .collect();
        assert_eq!(composed.len(), 1, "{:?}", outer.receipts);
        let outer_edit = outer
            .expr_edits
            .iter()
            .find(|edit| edit.receipt == "native-box-slice-access")
            .expect("the outer access edit");
        assert!(
            outer_edit.replacement.contains("ngrid[(i) as usize]"),
            "{:?}",
            outer_edit.replacement
        );
        let inner = plan_of("ngrid");
        assert!(
            !inner
                .expr_edits
                .iter()
                .any(|edit| outer_edit.span.contains(edit.span)),
            "the contained edit is dropped: {:?}",
            inner.expr_edits
        );
    })
    .unwrap();
}

/// The moved-out owner's shape is the FIELD transaction's: avl's rotations in
/// miniature — a load out of an owning field, a projection read and a
/// projection write through the loaded owner, and its close.
fn moved_out_fixture() -> String {
    format!(
        "{} #[repr(C)] pub struct R447Node {{ pub key: i32, pub next: *mut R447Node }}\n\
         pub unsafe fn drop_next(y: *mut R447Node) {{ \
           let mut x = (*y).next; (*y).next = 0 as *mut R447Node; \
           (*x).key = (*x).key + 1; \
           free(x as *mut core::ffi::c_void); }}",
        declarations()
    )
}

fn moved_out_plan(form: Option<&str>) -> Result<super::decision::box_facts::BoxPlan, String> {
    let input = moved_out_fixture();
    let form = form.map(str::to_owned);
    ::utils::compilation::run_compiler_on_str(&input, move |tcx| {
        match &form {
            Some(form) => {
                super::decision::ownership_fields_native::field_form_override::set(vec![(
                    "R447Node",
                    1,
                    form.as_str(),
                )])
            }
            None => super::decision::ownership_fields_native::field_form_override::clear(),
        }
        let (table, ctx) = super::decide_table_with_ctx_config(
            tcx,
            Some((
                super::A5Mode::PreciseReplay,
                Some(super::WholeProgramAttestation::FrozenBenchmarkGraph),
            )),
        )
        .unwrap();
        super::decision::ownership_fields_native::field_form_override::clear();
        let (_, decision) = table
            .entries
            .iter()
            .find(|(subject, _)| subject.param_name.as_deref() == Some("x"))
            .expect("drop_next::x");
        println!(
            "R447_AUDIT\n{}",
            ctx.raw_boundary_artifacts.ownership_native
        );
        match decision {
            Decision::Box(plan) => Ok(plan.clone()),
            other => Err(format!("{other:?}")),
        }
    })
    .unwrap()
}

/// R456-5 (relay 051, STOP 1 → (A)): the withdrawal's pin. The move out of an
/// owning field is rendered by the FIELD family — `field_reference`'s
/// `owned-field-move` writes `{inner}.take()` at the load's own span, keyed on
/// this producer's `Decision::Box(plan).optional` — so this producer writes
/// NOTHING at that span. R455-6(b) built the same text here for one commit and
/// the composition refused the second claim (`wrap-claim-refused:(481, 489)`
/// on `batch-12-dry14`; report 041 §2). What this producer still owns for a
/// moved-out owner is the type, the projections and the close.
#[test]
fn r455_the_moved_out_load_is_left_to_the_field_family() {
    let _serialise = super::decision::ownership_fields_native::field_form_override::LOCK
        .lock()
        .unwrap_or_else(|poisoned| poisoned.into_inner());
    let optional = moved_out_plan(Some("opt-box")).expect("opt-box form");
    assert!(
        !optional
            .expr_edits
            .iter()
            .any(|edit| edit.receipt == "native-box-moved-out-load"
                || edit.receipt == "native-owner-moved-out-of-a-field"),
        "the load's span stays unclaimed: {:?}",
        optional.expr_edits
    );
    // The rest of the moved-out owner is still delivered here.
    assert!(optional.optional);
    assert_eq!(
        optional
            .expr_edits
            .iter()
            .filter(|edit| edit.receipt == "native-box-optional-owner-projection")
            .count(),
        2,
        "{:?}",
        optional.expr_edits
    );
    assert!(
        optional
            .expr_edits
            .iter()
            .any(|edit| edit.receipt == "c-free-site-drop"),
        "{:?}",
        optional.expr_edits
    );
}

/// R456-5, the half that survives the withdrawal: a NON-optional owning field
/// has no renderable move — `(*y).next` is behind a raw deref, so a `Box<T>`
/// field cannot be moved out at all (`E0507`) and there is no null to leave
/// behind. The field family refuses the same shape on its own side
/// (`owned-move-needs-optional-box`), so holding here keeps one vocabulary
/// instead of typing a local whose initializer nobody can write.
#[test]
fn r455_a_non_optional_owning_field_holds_the_moved_out_owner() {
    let _serialise = super::decision::ownership_fields_native::field_form_override::LOCK
        .lock()
        .unwrap_or_else(|poisoned| poisoned.into_inner());
    let plain = moved_out_plan(Some("box"));
    assert!(plain.is_err(), "{plain:?}");
}

/// R447 (relay 044): the field transaction's own form decides the moved-out
/// owner's shape, and this lane's line now carries the query that asks it
/// (`owning_field_form`) instead of a patch. With no transaction the owner
/// holds, fail-closed; with a plain owning box it is a `Box<T>`; with
/// wave-6f's `opt-box` it is an `Option<Box<T>>` whose projections open the
/// option — shared to read, unique to write — which is R440-4's one shape.
#[test]
fn r447_a_moved_out_owner_takes_the_field_transactions_shape() {
    let _serialise = super::decision::ownership_fields_native::field_form_override::LOCK
        .lock()
        .unwrap_or_else(|poisoned| poisoned.into_inner());
    // R453-1: with no override the SEAM answers. On this line its body is the
    // stub (`None`), so the owner holds; on a composition whose join is live a
    // real transaction may own the field, and the owner is then a plan of the
    // shape that transaction delivers. Both are accepted; the three override
    // cases below stay exact on every frame, because the override answers
    // before the seam body does.
    match moved_out_plan(None) {
        Err(_) => {}
        Ok(plan) => assert!(
            plan.receipts.iter().any(|receipt| receipt
                .starts_with("native-box-declaration-type ::std::boxed::Box<")
                || receipt.starts_with(
                    "native-box-declaration-type ::std::option::Option<::std::boxed::Box<"
                )),
            "a joined frame delivers the transaction's shape: {:?}",
            plan.receipts
        ),
    }
    // A plain owning box: superseded by R455-6(b). While the field family
    // rendered the load, this shape delivered a `Box<T>` local; now that the
    // rendering is this producer's there is no move to write — the place is
    // behind a raw deref and the container has no `None` to keep — so the
    // shape holds. `r455_a_non_optional_owning_field_holds_the_moved_out_owner`
    // is the pin; here it is only the contrast with the optional form below.
    assert!(moved_out_plan(Some("box")).is_err(), "non-optional holds");
    // wave-6f's owning form: the local is optional and every projection
    // through it opens the option.
    let optional = moved_out_plan(Some("opt-box")).expect("opt-box form");
    assert!(optional.optional);
    assert!(
        optional.receipts.iter().any(|receipt| receipt
            == "native-box-declaration-type ::std::option::Option<::std::boxed::Box<crate::R447Node>>"),
        "{:?}",
        optional.receipts
    );
    let projections: Vec<&str> = optional
        .expr_edits
        .iter()
        .filter(|edit| edit.receipt == "native-box-optional-owner-projection")
        .map(|edit| edit.replacement.as_str())
        .collect();
    assert_eq!(
        projections
            .iter()
            .filter(|r| **r == "x.as_deref_mut().unwrap()")
            .count(),
        1,
        "the write opens uniquely: {projections:?}"
    );
    assert_eq!(
        projections
            .iter()
            .filter(|r| **r == "x.as_deref().unwrap()")
            .count(),
        1,
        "the read shares, so two reads in one expression coexist: {projections:?}"
    );
    // R450: a field delivered as an optional boxed SLICE gives the local the
    // same payload — only the type text moves, the projections are unchanged.
    let optional_slice = moved_out_plan(Some("opt-box-slice")).expect("opt-box-slice form");
    assert!(optional_slice.optional);
    assert!(
        optional_slice.receipts.iter().any(|receipt| receipt
            == "native-box-declaration-type ::std::option::Option<::std::boxed::Box<[crate::R447Node]>>"),
        "{:?}",
        optional_slice.receipts
    );
    assert_eq!(
        optional_slice
            .expr_edits
            .iter()
            .filter(|edit| edit.receipt == "native-box-optional-owner-projection")
            .count(),
        2,
        "the projections are unchanged by the payload's shape"
    );
    // The delivered shapes render the load as the move they can prove
    // (R455-6(b)) and nothing else: no allocation is constructed here, and the
    // source stage's marker edit never reaches the plan.
    for plan in [&optional, &optional_slice] {
        assert!(
            !plan
                .expr_edits
                .iter()
                .any(|edit| edit.receipt == "native-malloc-zero-numeric"
                    || edit.receipt == "native-owner-moved-out-of-a-field"),
            "{:?}",
            plan.expr_edits
        );
        assert!(
            !plan
                .expr_edits
                .iter()
                .any(|edit| edit.receipt == "native-box-moved-out-load"),
            "R456-5: the load is the field family's edit: {:?}",
            plan.expr_edits
        );
    }
}

/// R442 (report 033): an alias another family renders as a mutable slice over
/// this owner keeps the owner typed instead of holding it. IGNORED on this
/// base with the measured reason: no family here decides one of this
/// producer's view aliases, and the injection route does not reach the
/// bundle derivation (report 033 claim 6), so the rule is exercised on the
/// composition that carries wave-5d2's rule B — run it there with
/// `--ignored`.
#[test]
#[ignore = "composed gate: needs a family that decides this owner's view alias (wave-5d2 rule B)"]
fn r442_an_alias_another_family_renders_keeps_the_owner_typed() {
    let input = format!(
        "{} pub unsafe fn holder(width:i32,height:i32){{ let mut buf=calloc((width*height) as usize,core::mem::size_of::<f32>()) as *mut f32; let mut x=0; while x<width {{ let mut v=buf.offset((height*x) as isize); *v.offset(0)=1.0f32; sink(v,height); x+=1; }} free(buf as *mut core::ffi::c_void); }} unsafe fn sink(v:*mut f32,n:i32){{ let mut i=0; while i<n {{ *v.offset(i as isize)=0.0f32; i+=1; }} }}",
        declarations()
    );
    ::utils::compilation::run_compiler_on_str(&input, |tcx| {
        let (_, ctx) = super::decide_table_with_ctx_config(
            tcx,
            Some((
                super::A5Mode::PreciseReplay,
                Some(super::WholeProgramAttestation::FrozenBenchmarkGraph),
            )),
        )
        .unwrap();
        let audit = &ctx.raw_boundary_artifacts.ownership_native;
        let row = audit
            .lines()
            .find(|line| line.starts_with("holder::buf#"))
            .unwrap_or_else(|| panic!("{audit}"));
        assert!(
            !row.contains("native-view-alias-family-owned"),
            "the alias is the deciding family's to render: {row}"
        );
    })
    .unwrap();
}
