use rustc_hir::def::DefKind;
use rustc_middle::{
    mir::VarDebugInfoContents,
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
            let (param_name, arg_index, pairing_confidence) = match (first, second) {
                (Some(info), None) => match info.argument_index {
                    Some(arg_index) => (
                        Some(info.name.to_string()),
                        Some(arg_index as u32),
                        PairingConfidence::High,
                    ),
                    None => (None, None, PairingConfidence::Low),
                },
                _ => (None, None, PairingConfidence::Low),
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
                // Filled by the gated Codex follow-on (Track 2, T2.5). While
                // these are None everywhere, the span axis reports INACTIVE and
                // `span_axis_is_active_on_producer_b` is RED by design.
                binding_span_lo: None,
                binding_span_hi: None,
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
    /// at this body-query phase, so no deletion mutation exists for this test.
    /// It is a tripwire for a future body-query change that merges those locals.
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

        assert_eq!(rows.len(), 1);
        assert_eq!(rows[0].param_name.as_deref(), Some("pointer"));
        assert_eq!(rows[0].arg_index, Some(1));
        assert_eq!(rows[0].pairing_confidence, PairingConfidence::High);
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
}
