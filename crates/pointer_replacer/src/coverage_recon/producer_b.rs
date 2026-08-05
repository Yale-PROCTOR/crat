use rustc_hir::def::DefKind;
use rustc_middle::{
    mir::{Local, VarDebugInfoContents},
    ty::{TyCtxt, TyKind},
};

use super::schema::{PairingConfidence, Row, sort_rows};

#[allow(
    dead_code,
    reason = "no non-test consumer until the rewriter is wired into \
              the pipeline. EXPIRY-CORRECTED 2026-07-30: this reason used to \
              say 'consumers land at C.1/C.4'. Both landed and the allow is \
              still required, because both consumers are `cfg(test)` — a dated \
              promise that came due and did not settle. Targeted on the entry \
              point rather than module-wide: allowing an item makes it a live \
              root, so the lint stays active over everything reachable from it."
)]
pub(crate) fn rows(tcx: TyCtxt<'_>) -> Vec<Row> {
    let mut rows = Vec::new();

    for &did in tcx.mir_keys(()) {
        if tcx.def_kind(did) != DefKind::Fn {
            continue;
        }

        let body = tcx.mir_drops_elaborated_and_const_checked(did).borrow();
        let fn_path = tcx.def_path_str(did.to_def_id());

        for local in body.args_iter() {
            let mut ty = body.local_decls[local].ty;
            let mut ptr_depth = 0;
            while ptr_depth < 3 {
                ty = match ty.kind() {
                    TyKind::RawPtr(inner, _) | TyKind::Ref(_, inner, _) => *inner,
                    _ => break,
                };
                ptr_depth += 1;
            }
            if ptr_depth == 0 {
                continue;
            }

            let mut debug_entries = body.var_debug_info.iter().filter(|info| {
                matches!(
                    &info.value,
                    VarDebugInfoContents::Place(place)
                        if place.as_local() == Some(local)
                )
            });
            let first = debug_entries.next();
            let second = debug_entries.next();
            let (
                param_name,
                arg_index,
                pairing_confidence,
                binding_span_lo,
                binding_span_hi,
            ) = match (first, second) {
                (Some(info), None) => match info.argument_index {
                    Some(arg_index) => {
                        let source_map = tcx.sess.source_map();
                        let span = info.source_info.span;
                        let binding_span_lo =
                            Some(source_map.lookup_byte_offset(span.lo()).pos.0);
                        let binding_span_hi =
                            Some(source_map.lookup_byte_offset(span.hi()).pos.0);
                        (
                            Some(info.name.to_string()),
                            Some(arg_index as u32),
                            PairingConfidence::High,
                            binding_span_lo,
                            binding_span_hi,
                        )
                    }
                    None => (None, None, PairingConfidence::Low, None, None),
                },
                _ => (None, None, PairingConfidence::Low, None, None),
            };

            rows.push(Row {
                fn_path: fn_path.clone(),
                mir_local: local.as_u32(),
                param_name,
                arg_index,
                ptr_depth,
                pairing_confidence,
                decl_span: None,
                decl_span_lo: None,
                decl_span_hi: None,
                binding_span_lo,
                binding_span_hi,
                decl_shape: None,
                outcome: None,
                degrade_reason: None,
            });
        }

        for local_index in body.arg_count + 1..=body.local_decls.len() - 1 {
            let local = Local::from_usize(local_index);
            let mut ty = body.local_decls[local].ty;
            let mut ptr_depth = 0;
            while ptr_depth < 3 {
                ty = match ty.kind() {
                    TyKind::RawPtr(inner, _) | TyKind::Ref(_, inner, _) => *inner,
                    _ => break,
                };
                ptr_depth += 1;
            }
            if ptr_depth == 0 {
                continue;
            }

            let mut debug_entries = body.var_debug_info.iter().filter(|info| {
                matches!(
                    &info.value,
                    VarDebugInfoContents::Place(place)
                        if place.as_local() == Some(local)
                )
            });
            let first = debug_entries.next();
            let second = debug_entries.next();
            if first.is_none() {
                continue;
            }

            let paired_info: Option<&rustc_middle::mir::VarDebugInfo<'_>> =
                match (first, second) {
                    (Some(info), None) if info.argument_index.is_none() => Some(info),
                    (Some(info), None) => {
                        assert!(
                            info.argument_index.is_none(),
                            "non-parameter MIR local {local:?} unexpectedly carries argument_index {:?}",
                            info.argument_index
                        );
                        None
                    }
                    (Some(_), Some(_)) => None,
                    _ => None,
                };
            let (param_name, pairing_confidence, binding_span_lo, binding_span_hi) =
                match paired_info {
                    Some(info) => {
                        let source_map = tcx.sess.source_map();
                        let span = info.source_info.span;
                        (
                            Some(info.name.to_string()),
                            PairingConfidence::High,
                            Some(source_map.lookup_byte_offset(span.lo()).pos.0),
                            Some(source_map.lookup_byte_offset(span.hi()).pos.0),
                        )
                    }
                    None => (None, PairingConfidence::Low, None, None),
                };

            rows.push(Row {
                fn_path: fn_path.clone(),
                mir_local: local.as_u32(),
                param_name,
                arg_index: None,
                ptr_depth,
                pairing_confidence,
                decl_span: None,
                decl_span_lo: None,
                decl_span_hi: None,
                binding_span_lo,
                binding_span_hi,
                decl_shape: None,
                outcome: None,
                degrade_reason: None,
            });
        }
    }

    sort_rows(&mut rows);
    rows
}

#[cfg(test)]
mod binding_span_witnesses {
    extern crate rustc_driver;
    extern crate rustc_interface;

    use std::{
        fs,
        path::{Path, PathBuf},
        sync::atomic::{AtomicUsize, Ordering},
    };

    use rustc_driver::{Callbacks, Compilation, run_compiler};
    use rustc_interface::interface;
    use rustc_middle::ty::TyCtxt;

    use super::{Row, rows};

    static NEXT_FIXTURE: AtomicUsize = AtomicUsize::new(0);

    #[derive(Default)]
    struct CaptureRows {
        rows: Vec<Row>,
    }

    impl Callbacks for CaptureRows {
        fn after_analysis<'tcx>(
            &mut self,
            _compiler: &interface::Compiler,
            tcx: TyCtxt<'tcx>,
        ) -> Compilation {
            self.rows = rows(tcx);
            Compilation::Stop
        }
    }

    struct FixtureDir(PathBuf);

    impl FixtureDir {
        fn new() -> Self {
            let sequence = NEXT_FIXTURE.fetch_add(1, Ordering::Relaxed);
            let path = std::env::temp_dir().join(format!(
                "pointer-replacer-binding-span-{}-{sequence}",
                std::process::id()
            ));
            fs::create_dir(&path).expect("create binding-span fixture directory");
            Self(path)
        }

        fn path(&self) -> &Path {
            &self.0
        }
    }

    impl Drop for FixtureDir {
        fn drop(&mut self) {
            let _ = fs::remove_dir_all(&self.0);
        }
    }

    fn rows_for_fixture(root_source: &str, extra_files: &[(&str, &str)]) -> Vec<Row> {
        let fixture_dir = FixtureDir::new();
        let input = fixture_dir.path().join("lib.rs");
        fs::write(&input, root_source).expect("write binding-span fixture root");
        for &(name, source) in extra_files {
            fs::write(fixture_dir.path().join(name), source)
                .expect("write binding-span fixture module");
        }

        let args = vec![
            "rustc".to_owned(),
            input.to_string_lossy().into_owned(),
            "--crate-name=binding_span_witness".to_owned(),
            "--crate-type=lib".to_owned(),
            "--edition=2021".to_owned(),
            "--emit=metadata".to_owned(),
            format!("--out-dir={}", fixture_dir.path().display()),
        ];
        let mut capture = CaptureRows::default();
        run_compiler(&args, &mut capture);
        capture.rows
    }

    fn row_for<'a>(rows: &'a [Row], fn_suffix: &str) -> &'a Row {
        rows.iter()
            .find(|row| row.fn_path.ends_with(fn_suffix))
            .unwrap_or_else(|| panic!("missing producer-B row for {fn_suffix}"))
    }

    #[test]
    fn binding_span_is_present_on_named_parameters() {
        let rows = rows_for_fixture(
            "#![allow(dead_code, unused_variables)]\nfn named(first: *mut i32, second: *mut i32) {}\n",
            &[],
        );
        let named_rows: Vec<_> = rows
            .iter()
            .filter(|row| row.fn_path.ends_with("named"))
            .collect();

        assert_eq!(named_rows.len(), 2);
        for row in named_rows {
            assert!(row.binding_span_lo.is_some());
            assert!(row.binding_span_hi.is_some());
        }
    }

    /// Positive control only: the reachable non-High case has no debug entry,
    /// so no deletion can expose a span source for this parameter.
    #[test]
    fn binding_span_is_absent_on_unnamed_parameter_positive_control() {
        let rows = rows_for_fixture(
            "#![allow(dead_code)]\nfn unnamed(_: *mut i32) {}\n",
            &[],
        );
        let row = row_for(&rows, "unnamed");

        assert_eq!(row.binding_span_lo, None);
        assert_eq!(row.binding_span_hi, None);
    }

    #[test]
    fn binding_span_uses_file_relative_offsets() {
        let fixture_source =
            "#![allow(dead_code, unused_variables)]\npub fn coordinate_target(coordinate_param: *mut i32) {}\n";
        let rows = rows_for_fixture(
            "#![allow(dead_code)]\nmod padding;\nmod fixture;\n",
            &[
                (
                    "padding.rs",
                    "#![allow(dead_code)]\npub static PADDING: [u8; 64] = [0; 64];\n",
                ),
                ("fixture.rs", fixture_source),
            ],
        );
        let row = row_for(&rows, "fixture::coordinate_target");
        let expected = fixture_source
            .find("coordinate_param")
            .expect("coordinate parameter occurs in fixture") as u32;

        assert_eq!(row.binding_span_lo, Some(expected));
        // The END bound, in the SAME file-relative system. Without this, `hi` is
        // constrained only by `lo < hi`, which a raw `BytePos` satisfies — so a
        // hi-only coordinate regression survived the whole unit suite and waited
        // for the corpus interleave to notice it.
        assert_eq!(
            row.binding_span_hi,
            Some(expected + "coordinate_param".len() as u32)
        );
    }

    #[test]
    fn binding_span_bounds_are_strictly_ordered() {
        let rows = rows_for_fixture(
            "#![allow(dead_code, unused_variables)]\nfn ordered(parameter: *mut i32) {}\n",
            &[],
        );
        let row = row_for(&rows, "ordered");
        let (lo, hi) = row
            .binding_span_lo
            .zip(row.binding_span_hi)
            .expect("named parameter has both binding-span bounds");

        assert!(lo < hi, "binding span must be nonempty: {lo}..{hi}");
    }
}

#[cfg(test)]
mod tests {
    use super::rows;
    use crate::coverage_recon::schema::{PairingConfidence, Row};

    fn fixture_rows(code: &str) -> Vec<Row> {
        ::utils::compilation::run_compiler_on_str(code, rows)
            .expect("fixture should compile")
            .into_iter()
            .filter(|row| row.fn_path.rsplit("::").next() == Some("f"))
            .collect()
    }

    /// Deleting the `var_debug_info` lookup makes both names `None` and fails
    /// this witness.
    #[test]
    fn pairs_named_pointer_parameters_in_source_order() {
        let rows = fixture_rows(
            r#"
            #![allow(dead_code, unused_variables)]
            fn f(first: *mut i32, second: *const u8) {}
            "#,
        );

        let pairing: Vec<_> = rows
            .iter()
            .map(|row| {
                (
                    row.mir_local,
                    row.param_name.as_deref(),
                    row.arg_index,
                    row.pairing_confidence,
                )
            })
            .collect();
        assert_eq!(
            pairing,
            vec![
                (1, Some("first"), Some(1), PairingConfidence::High),
                (2, Some("second"), Some(2), PairingConfidence::High),
            ]
        );
    }

    /// Positive control: the shadowing body binding receives a fresh MIR local
    /// at this body-query phase, so it cannot contaminate the parameter row.
    /// The locals universe emits that fresh binding separately. No deletion
    /// mutation exists for the parameter-pairing invariant this test pins.
    #[test]
    fn ignores_a_later_shadowing_binding() {
        let rows = fixture_rows(
            r#"
            #![allow(dead_code, unused_variables)]
            fn f(pointer: *mut i32) {
                let pointer = pointer;
                let _ = pointer;
            }
            "#,
        );

        let pairing: Vec<_> = rows
            .iter()
            .map(|row| {
                (
                    row.mir_local,
                    row.param_name.as_deref(),
                    row.arg_index,
                    row.pairing_confidence,
                )
            })
            .collect();
        assert_eq!(
            pairing,
            vec![
                (1, Some("pointer"), Some(1), PairingConfidence::High),
                (2, Some("pointer"), None, PairingConfidence::High),
            ]
        );
    }

    /// Replacing the entry-count branch with unconditional `High` fails this
    /// witness.
    #[test]
    fn marks_an_unnamed_parameter_low_confidence() {
        let rows = fixture_rows(
            r#"
            #![allow(dead_code)]
            fn f(_: *mut i32) {}
            "#,
        );

        assert_eq!(rows.len(), 1);
        assert_eq!(rows[0].param_name, None);
        assert_eq!(rows[0].arg_index, None);
        assert_eq!(rows[0].pairing_confidence, PairingConfidence::Low);
    }

    /// Deleting the `depth > 0` guard emits the scalar parameter and fails this
    /// witness.
    #[test]
    fn counts_pointer_depth_and_omits_non_pointers() {
        let rows = fixture_rows(
            r#"
            #![allow(dead_code, unused_variables)]
            fn f(nested: *mut *mut i32, scalar: i32) {}
            "#,
        );

        assert_eq!(rows.len(), 1);
        assert_eq!(rows[0].param_name.as_deref(), Some("nested"));
        assert_eq!(rows[0].ptr_depth, 2);
    }

    /// Positive control: MIR types are already resolved, so producer B sees
    /// through aliases without an alias-handling branch. No deletion mutation
    /// exists for this test.
    #[test]
    fn resolved_alias_typed_parameter_has_depth_one() {
        let rows = fixture_rows(
            r#"
            #![allow(dead_code, unused_variables, non_camel_case_types)]
            struct S;
            pub type handle_t = *mut S;
            fn f(h: handle_t) {}
            "#,
        );

        assert_eq!(rows.len(), 1);
        assert_eq!(rows[0].param_name.as_deref(), Some("h"));
        assert_eq!(rows[0].ptr_depth, 1);
    }

    /// L1: deleting the local `argument_index.is_none()` arm makes `_2`
    /// low-confidence and fails this witness.
    #[test]
    fn locals_plain_named_binding_is_high_confidence() {
        let rows = fixture_rows(
            r#"
            #![allow(dead_code, unused_variables)]
            unsafe fn f(q: *mut i32) -> i32 {
                let p: *mut i32 = q;
                *p = 1;
                *p + *q
            }
            "#,
        );

        let pairing: Vec<_> = rows
            .iter()
            .map(|row| {
                (
                    row.mir_local,
                    row.param_name.as_deref(),
                    row.arg_index,
                    row.pairing_confidence,
                )
            })
            .collect();
        assert_eq!(
            pairing,
            vec![
                (1, Some("q"), Some(1), PairingConfidence::High),
                (2, Some("p"), None, PairingConfidence::High),
            ]
        );
    }

    /// L2: deleting the locals-row emission removes both shadow bindings and
    /// fails this witness; the two equal names must not be used as row keys.
    #[test]
    fn locals_shadowed_bindings_remain_distinct_rows() {
        let rows = fixture_rows(
            r#"
            #![allow(dead_code, unused_variables)]
            unsafe extern "C" {
                fn malloc(size: usize) -> *mut core::ffi::c_void;
            }
            unsafe fn f() -> i32 {
                let p: *mut i32 = malloc(4) as *mut i32;
                *p = 1;
                let p: *mut i32 = malloc(4) as *mut i32;
                *p = 2;
                *p
            }
            "#,
        );

        let pairing: Vec<_> = rows
            .iter()
            .map(|row| {
                (
                    row.mir_local,
                    row.param_name.as_deref(),
                    row.arg_index,
                    row.pairing_confidence,
                )
            })
            .collect();
        assert_eq!(
            pairing,
            vec![
                (1, Some("p"), None, PairingConfidence::High),
                (3, Some("p"), None, PairingConfidence::High),
            ]
        );
    }

    /// L3: deleting the zero-entry exclusion emits the pointer temporary and
    /// fails this witness.
    #[test]
    fn locals_bare_pointer_temporary_is_excluded() {
        let rows = fixture_rows(
            r#"
            #![allow(dead_code, unused_variables)]
            unsafe extern "C" {
                fn malloc(size: usize) -> *mut core::ffi::c_void;
            }
            unsafe fn f() -> i32 {
                *(malloc(4) as *mut i32) = 3;
                0
            }
            "#,
        );

        assert!(rows.is_empty());
    }

    /// L4: deleting the locals range's `arg_count + 1` lower bound admits the
    /// named parameter and fires the local contradiction assertion.
    #[test]
    fn locals_and_parameters_are_disjoint_universes() {
        let rows = fixture_rows(
            r#"
            #![allow(dead_code, unused_variables)]
            unsafe fn f(q: *mut i32) -> i32 {
                let p: *mut i32 = q;
                *p = 1;
                *p + *q
            }
            "#,
        );

        let keys: Vec<_> = rows
            .iter()
            .map(|row| (row.mir_local, row.arg_index))
            .collect();
        assert_eq!(keys, vec![(1, Some(1)), (2, None)]);
    }

    /// L5: deleting the depth test emits tuple parameter `_1` and fails this
    /// witness; its component bindings `_2` and `_3` are ordinary locals rows.
    #[test]
    fn locals_pattern_parameter_components_are_rows() {
        let rows = fixture_rows(
            r#"
            #![allow(dead_code, unused_variables)]
            unsafe fn f((a, b): (*mut i32, *mut i32)) -> i32 {
                *a + *b
            }
            "#,
        );

        let pairing: Vec<_> = rows
            .iter()
            .map(|row| {
                (
                    row.mir_local,
                    row.param_name.as_deref(),
                    row.arg_index,
                    row.pairing_confidence,
                )
            })
            .collect();
        assert_eq!(
            pairing,
            vec![
                (2, Some("a"), None, PairingConfidence::High),
                (3, Some("b"), None, PairingConfidence::High),
            ]
        );
    }

    /// L6: deleting the locals-loop depth test emits scalar local `_1` while
    /// leaving pointer local `_2` unchanged, and fails this witness.
    #[test]
    fn locals_named_scalar_is_excluded_beside_pointer_local() {
        let rows = fixture_rows(
            r#"
            #![allow(dead_code, unused_variables)]
            unsafe fn f() -> i32 {
                let n: i32 = 5;
                let p: *const i32 = &n;
                *p
            }
            "#,
        );

        let pairing: Vec<_> = rows
            .iter()
            .map(|row| {
                (
                    row.mir_local,
                    row.param_name.as_deref(),
                    row.arg_index,
                    row.ptr_depth,
                    row.pairing_confidence,
                )
            })
            .collect();
        assert_eq!(
            pairing,
            vec![(
                2,
                Some("p"),
                None,
                1,
                PairingConfidence::High,
            )]
        );
    }
}
