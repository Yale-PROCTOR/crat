//! Read-only native evidence export for the approved diagnostic census.

use std::{
    fmt::Write as _,
    io::Write as _,
    sync::atomic::{AtomicUsize, Ordering},
};

use rustc_middle::ty::{TyCtxt, TyKind};

use crate::bo_rewriter::{DecideCtx, decision::DecisionTable};

pub(super) fn snapshot(
    tcx: TyCtxt<'_>,
    table: &DecisionTable,
    ctx: &DecideCtx,
) -> (String, String) {
    let mut positions = String::from(
        "caller\tcallee\targument_index\tsite\tmir_site\tverdict\texpected\tfound\tformal_mutability\tpeer_receipts\tworld\tguard\n",
    );
    for (row, proof) in super::diagnose(table, &ctx.mut_facts)
        .iter()
        .zip(&table.seams.overlap_proofs)
    {
        let mutable = match row.formal_mutability {
            super::NativeMutability::Missing => "missing",
            super::NativeMutability::Present { mutable: true } => "mutable",
            super::NativeMutability::Present { mutable: false } => "immutable",
        };
        writeln!(
            positions,
            "{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}",
            tcx.def_path_str(proof.caller.to_def_id()),
            tcx.def_path_str(proof.callee.to_def_id()),
            proof.index,
            tcx.sess.source_map().span_to_diagnostic_string(proof.span),
            proof
                .proof_site_key
                .map_or_else(|| "missing".into(), |key| key.receipt_key()),
            proof.verdict.key(),
            row.expected.key(),
            row.found.key(),
            mutable,
            proof.peer_receipts,
            proof.world,
            proof.guard
        )
        .unwrap();
    }
    let mut functions = ctx
        .subjects
        .iter()
        .map(|subject| subject.fn_did)
        .collect::<Vec<_>>();
    functions.sort_by_key(|did| did.local_def_index.as_u32());
    functions.dedup();
    let mut formals =
        String::from("callee\targument_index\tmutability\tdefaulted\toriginal_type\n");
    for function in functions {
        let body = tcx.optimized_mir(function);
        for (index, local) in body.args_iter().enumerate() {
            let ty = body.local_decls[local].ty;
            if !matches!(ty.kind(), TyKind::RawPtr(..) | TyKind::Ref(..)) {
                continue;
            }
            let defaulted = ctx.mut_facts.is_defaulted(function, local);
            let mutable = if defaulted {
                "missing"
            } else if ctx.mut_facts.is_mutable(function, local) {
                "mutable"
            } else {
                "immutable"
            };
            writeln!(
                formals,
                "{}\t{index}\t{mutable}\t{defaulted}\t{ty}",
                tcx.def_path_str(function.to_def_id())
            )
            .unwrap();
        }
    }
    (positions, formals)
}

pub(crate) fn publish(
    tcx: TyCtxt<'_>,
    table: &DecisionTable,
    ctx: &DecideCtx,
) -> Result<(), String> {
    let Some(root) = std::env::var_os("CRAT_WAVE5P_DIAGNOSTIC_DIR") else { return Ok(()) };
    let program = std::env::var("CRAT_ERA5_PROGRAM")
        .map_err(|error| format!("wave5p-observer-program:{error}"))?;
    if program.is_empty()
        || !program
            .bytes()
            .all(|byte| byte.is_ascii_alphanumeric() || b"._-".contains(&byte))
    {
        return Err("wave5p-observer-invalid-program".into());
    }
    let root = std::path::PathBuf::from(root);
    std::fs::create_dir_all(&root).map_err(|error| format!("wave5p-observer-directory:{error}"))?;
    static NEXT: AtomicUsize = AtomicUsize::new(0);
    let prefix = format!(
        "{program}.{}.{}",
        std::process::id(),
        NEXT.fetch_add(1, Ordering::Relaxed)
    );
    let (positions, formals) = snapshot(tcx, table, ctx);
    // Retain every callback separately. Repeated snapshots can be reconciled
    // by identity without overwriting evidence or altering the decision table.
    for (suffix, text) in [("positions", positions), ("formals", formals)] {
        let path = root.join(format!("{prefix}.{suffix}.tsv"));
        let mut file = std::fs::OpenOptions::new()
            .write(true)
            .create_new(true)
            .open(path)
            .map_err(|error| format!("wave5p-observer-create:{error}"))?;
        file.write_all(text.as_bytes())
            .map_err(|error| format!("wave5p-observer-write:{error}"))?;
    }
    Ok(())
}
