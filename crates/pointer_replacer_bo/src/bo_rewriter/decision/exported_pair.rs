//! wave-6a: **the exported-pair closure** (relay wave-6a/017 §1, R427-4).
//!
//! Under R415-7 each crate is the whole program, so a `#[no_mangle]` export
//! with no in-crate caller is not "unknown": its caller is the C surface, and
//! the exposure family's raw wrapper IS that caller — `Box::into_raw` on the
//! way out of an owning return, `Box::from_raw` on the way into an owning
//! formal (report 010's arms). A pointee may therefore convert even though
//! nothing in the crate calls the pair, PROVIDED the surface is closed: every
//! block that crosses it was allocated by our own allocator and is released
//! by it, never by libc's `free` on a Rust block or the reverse.
//!
//! **The first cut (R427-4).** A pointee `T` closes when, in the whole crate:
//! every function whose signature mentions `*mut T` / `*const T` is either a
//! PRODUCER (returns it) or a CONSUMER (takes it and frees it exactly once),
//! every one of them is exported, there is at least one of each, and no
//! struct field anywhere holds a `T` pointer — a field would let the pointer
//! be stored and released somewhere this rule cannot see. Anything else about
//! `T` — a third function taking it as a lend, a field of another struct, a
//! producer that is not exported — HOLDS the whole pair (fail-closed), and
//! the receipt says which: `exported-pair-closure:<pointee>:<detail>`.
//!
//! The closure is a PREMISE, not a plan: the allocation-return certificate
//! reads it to admit a callee with no receivers, and the Box-parameter chain
//! reads it to admit a consuming callee with no in-crate callers. Both still
//! prove everything else they normally prove.

use rustc_hash::{FxHashMap, FxHashSet};
use rustc_hir::def_id::{DefId, LocalDefId};
use rustc_middle::ty::{Ty, TyCtxt, TyKind};

/// The pointees whose exported surface is closed, with the receipts.
#[derive(Clone, Debug, Default)]
pub(crate) struct Closure {
    pointees: FxHashSet<DefId>,
    pub(crate) receipts: Vec<String>,
}

impl Closure {
    /// Is this pointee's exported surface closed?
    pub(crate) fn closes(&self, tcx: TyCtxt<'_>, pointee: Ty<'_>) -> bool {
        match pointee.kind() {
            TyKind::Adt(adt, _) => self.pointees.contains(&adt.did()),
            _ => {
                let _ = tcx;
                false
            }
        }
    }

    pub(crate) fn receipts_tsv(&self) -> String {
        let mut out = String::from("pointee\tkind\tdetail\n");
        let mut receipts = self.receipts.clone();
        receipts.sort();
        for receipt in receipts {
            out.push_str(&receipt);
            out.push('\n');
        }
        out
    }
}

/// Every depth-1 raw pointee an ADT signature position mentions.
fn signature_pointees<'tcx>(tcx: TyCtxt<'tcx>, function: LocalDefId) -> (Vec<DefId>, Vec<DefId>) {
    let signature = tcx.fn_sig(function.to_def_id()).skip_binder().skip_binder();
    let adt_of = |ty: Ty<'tcx>| match ty.kind() {
        TyKind::RawPtr(pointee, _) => match pointee.kind() {
            TyKind::Adt(adt, _) => Some(adt.did()),
            _ => None,
        },
        _ => None,
    };
    (
        signature.output().pipe(adt_of).into_iter().collect(),
        signature
            .inputs()
            .iter()
            .filter_map(|ty| adt_of(*ty))
            .collect(),
    )
}

trait Pipe: Sized {
    fn pipe<T>(self, f: impl FnOnce(Self) -> T) -> T {
        f(self)
    }
}

impl<T> Pipe for T {}

/// Derive the closure. `frees_formal` answers "does this function free the
/// formal at this index exactly once, with every other use rewritable?" — the
/// Box-parameter chain's own syntactic consumer test.
/// The C surface: the crate exports this symbol under its own name, so a
/// client outside the crate can call it. With the corpus' `explicit-empty`
/// configured exposure the exposure family surfaces only fn-pointer-web
/// members, so this — not `raw_surface` — is what "exported" means for the
/// closure; an unsurfaced export keeps its converted `extern "C"` signature,
/// which R415-7 rules admissible (relay wave-6a/015 STOP 2).
pub(crate) fn exported(tcx: TyCtxt<'_>, function: LocalDefId) -> bool {
    let did = function.to_def_id();
    tcx.get_attrs(did, rustc_span::sym::no_mangle)
        .next()
        .is_some()
        || tcx
            .get_attrs(did, rustc_span::sym::export_name)
            .next()
            .is_some()
}

pub(crate) fn derive<'tcx>(
    tcx: TyCtxt<'tcx>,
    functions: &[LocalDefId],
    raw_surface: &dyn Fn(LocalDefId) -> bool,
    consuming: &FxHashSet<(DefId, usize)>,
) -> Closure {
    let _ = raw_surface;
    let mut out = Closure::default();
    #[derive(Default)]
    struct Uses {
        producers: Vec<LocalDefId>,
        consumers: Vec<LocalDefId>,
        other: Vec<String>,
    }
    let mut by_pointee: FxHashMap<DefId, Uses> = FxHashMap::default();
    for &function in functions {
        let path = tcx.def_path_str(function.to_def_id());
        let (returns, inputs) = signature_pointees(tcx, function);
        for pointee in returns {
            by_pointee
                .entry(pointee)
                .or_default()
                .producers
                .push(function);
        }
        let signature = tcx.fn_sig(function.to_def_id()).skip_binder().skip_binder();
        for (index, input) in signature.inputs().iter().enumerate() {
            let TyKind::RawPtr(inner, _) = input.kind() else { continue };
            let TyKind::Adt(adt, _) = inner.kind() else { continue };
            let entry = by_pointee.entry(adt.did()).or_default();
            if consuming.contains(&(function.to_def_id(), index)) {
                entry.consumers.push(function);
            } else {
                entry.other.push(format!("{path}#{index}"));
            }
        }
        let _ = inputs;
    }
    // A `T` pointer inside ANY struct field can be stored and released where
    // this rule cannot see it.
    let mut fielded: FxHashSet<DefId> = FxHashSet::default();
    for id in tcx.hir_free_items() {
        if !matches!(
            tcx.hir_item(id).kind,
            rustc_hir::ItemKind::Struct(..) | rustc_hir::ItemKind::Union(..)
        ) {
            continue;
        }
        let adt = tcx.adt_def(id.owner_id.def_id);
        for variant in adt.variants() {
            for field in &variant.fields {
                let ty = tcx.type_of(field.did).skip_binder();
                if let TyKind::RawPtr(pointee, _) = ty.kind()
                    && let TyKind::Adt(inner, _) = pointee.kind()
                {
                    fielded.insert(inner.did());
                }
            }
        }
    }
    let mut pointees: Vec<(DefId, Uses)> = by_pointee.into_iter().collect();
    pointees.sort_by_key(|(did, _)| (did.krate.as_u32(), did.index.as_u32()));
    for (pointee, uses) in pointees {
        let path = tcx.def_path_str(pointee);
        let hold = |detail: String, out: &mut Closure| {
            out.receipts.push(format!(
                "{path}\theld\texported-pair-closure:{path}:{detail}"
            ));
        };
        if uses.producers.is_empty() || uses.consumers.is_empty() {
            continue;
        }
        if !uses.other.is_empty() {
            hold(
                format!("other-signature:{}", uses.other.join(",")),
                &mut out,
            );
            continue;
        }
        if fielded.contains(&pointee) {
            hold("struct-field".to_owned(), &mut out);
            continue;
        }
        if let Some(open) = uses
            .producers
            .iter()
            .chain(&uses.consumers)
            .find(|f| !exported(tcx, **f))
        {
            hold(
                format!("not-exported:{}", tcx.def_path_str(open.to_def_id())),
                &mut out,
            );
            continue;
        }
        out.pointees.insert(pointee);
        out.receipts.push(format!(
            "{path}\tclosed\texported-pair-closure:{path} producers={} consumers={}",
            uses.producers
                .iter()
                .map(|f| tcx.def_path_str(f.to_def_id()))
                .collect::<Vec<_>>()
                .join(","),
            uses.consumers
                .iter()
                .map(|f| tcx.def_path_str(f.to_def_id()))
                .collect::<Vec<_>>()
                .join(","),
        ));
    }
    out
}
