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
        degradations,
        first_diags,
        ..
    } = outcome
    else {
        panic!("{outcome:?}")
    };
    println!("R395_EMITTED_BEGIN {owner_name}\n{source}\nR395_EMITTED_END");
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
    println!(
        "R395_OUTCOME reverted={reverted_count} degradations={:?} first_diags={first_diags:?}",
        degradations
            .iter()
            .map(|d| (d.subject.clone(), d.reason.key(), d.reason.detail()))
            .collect::<Vec<_>>()
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
    assert!(s.contains("let mut img: ::std::boxed::Box<crate::heman_image_s> = ::std::boxed::Box::new(crate::heman_image_s { width: 0i32, height: 0i32, nbands: 0i32, data: ::core::ptr::null_mut() });"), "{s}");
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
        s.contains("::std::boxed::Box::new(crate::Pair { x: 0i32, y: 0i32 })"),
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
    let decided = |owner: &str| {
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
                .find(|(s, _)| s.param_name.as_deref() == Some(owner))
                .unwrap();
            let Decision::Box(plan) = decision else { panic!("{decision:?}") };
            assert_eq!(plan.shape, BoxShape::Slice);
            assert!(
                plan.receipts
                    .iter()
                    .any(|r| r.contains("disjoint=fresh-allocation-derivation-closure")),
                "{:?}",
                plan.receipts
            );
            let _ = &ctx;
        })
        .unwrap();
    };
    decided("pl1");
    decided("pl2");
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
        ..
    } = outcome
    else {
        panic!("{outcome:?}")
    };
    for owner in [
        "transform_to_coordfield::pl1#13",
        "transform_to_coordfield::pl2#21",
    ] {
        let row = degradations
            .iter()
            .find(|d| d.subject == owner)
            .expect(owner);
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
        // R402-2(b): the withdrawn Box row is DEGRADED in the E1 seed with its
        // withdrawal reason (never a placed box row) and is no custody
        // expectation, so the strict instrument sees no inferred-type claim.
        let seed = e1_subject_receipt
            .lines()
            .find(|line| line.starts_with(&format!("{owner}\t")))
            .unwrap_or_else(|| panic!("{owner} seed row: {e1_subject_receipt}"));
        let columns: Vec<&str> = seed.split('\t').collect();
        assert_eq!(columns[7], "degraded", "{seed}");
        assert_eq!(columns[8], "box-withdrawn-at-emission", "{seed}");
        assert!(columns[9].starts_with("signature-class-held:"), "{seed}");
        assert_eq!(columns[11], "0", "{seed}");
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
