use rustc_ast::{GenericParam, GenericParamKind, Generics};
use rustc_hash::{FxHashMap, FxHashSet};
use rustc_hir as hir;
use rustc_middle::{
    mir::{Local, RETURN_PLACE},
    ty::TyCtxt,
};
use rustc_span::{DUMMY_SP, Ident, Symbol, def_id::LocalDefId};

use super::Analysis;
use crate::{
    analyses::borrow::{
        StructFieldSlot,
        lifetime_flow::{LifetimeFlowSummary, SignatureRoot, SignatureSlot},
    },
    utils::rustc::RustProgram,
};

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct FnLifetimePlan {
    pub input_lifetimes: Vec<Option<Symbol>>,
    pub output_lifetime: Option<Symbol>,
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct StructLifetimePlan {
    pub field_lifetimes: FxHashMap<usize, Symbol>,
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct LifetimePlans {
    pub functions: FxHashMap<LocalDefId, FnLifetimePlan>,
    pub structs: FxHashMap<LocalDefId, StructLifetimePlan>,
}

impl LifetimePlans {
    pub fn new(input: &RustProgram<'_>, analysis: &Analysis) -> Self {
        Self {
            functions: function_lifetime_plans(input, analysis),
            structs: struct_lifetime_plans(input.tcx, analysis),
        }
    }
}

fn generated_lifetime_param(name: Symbol) -> GenericParam {
    let name = Symbol::intern(&format!("'{}", name.as_str().trim_start_matches('\'')));
    GenericParam {
        id: rustc_ast::DUMMY_NODE_ID,
        ident: Ident::new(name, DUMMY_SP),
        attrs: Default::default(),
        bounds: vec![],
        is_placeholder: false,
        kind: GenericParamKind::Lifetime,
        colon_span: None,
    }
}

fn existing_lifetime_params(generics: &Generics) -> FxHashSet<Symbol> {
    generics
        .params
        .iter()
        .filter(|param| matches!(param.kind, GenericParamKind::Lifetime))
        .map(|param| Symbol::intern(param.ident.name.as_str().trim_start_matches('\'')))
        .collect()
}

pub(super) fn ensure_lifetime_params(generics: &mut Generics, lifetimes: &[Symbol]) {
    let mut existing = existing_lifetime_params(generics);
    let mut insert_at = generics
        .params
        .iter()
        .position(|param| !matches!(param.kind, GenericParamKind::Lifetime))
        .unwrap_or(generics.params.len());

    for lifetime in lifetimes {
        if !existing.insert(*lifetime) {
            continue;
        }
        generics
            .params
            .insert(insert_at, generated_lifetime_param(*lifetime));
        insert_at += 1;
    }
}

#[derive(Default)]
struct LifetimeNameAllocator {
    used: FxHashSet<Symbol>,
}

impl LifetimeNameAllocator {
    fn with_existing<I>(existing: I) -> Self
    where I: IntoIterator<Item = Symbol> {
        Self {
            used: existing.into_iter().collect(),
        }
    }

    fn next(&mut self) -> Symbol {
        for ch in b'a'..=b'z' {
            let name = Symbol::intern(std::str::from_utf8(&[ch]).unwrap());
            if self.used.insert(name) {
                return name;
            }
        }
        let mut index = 0usize;
        loop {
            let name = Symbol::intern(&format!("lt{index}"));
            if self.used.insert(name) {
                return name;
            }
            index += 1;
        }
    }
}

fn existing_hir_lifetime_params(tcx: TyCtxt<'_>, did: LocalDefId) -> Vec<Symbol> {
    let hir::Node::Item(item) = tcx.hir_node_by_def_id(did) else {
        return vec![];
    };
    let Some(generics) = item.kind.generics() else {
        return vec![];
    };
    generics
        .params
        .iter()
        .filter(|param| matches!(param.kind, hir::GenericParamKind::Lifetime { .. }))
        .map(|param| Symbol::intern(param.name.ident().name.as_str().trim_start_matches('\'')))
        .collect()
}

fn function_lifetime_plans(
    input: &RustProgram<'_>,
    analysis: &Analysis,
) -> FxHashMap<LocalDefId, FnLifetimePlan> {
    let mut plans = FxHashMap::default();

    for did in input.functions.iter().copied() {
        let body = input
            .tcx
            .mir_drops_elaborated_and_const_checked(did)
            .borrow();
        let return_decl = &body.local_decls[RETURN_PLACE];
        if !return_decl.ty.is_raw_ptr() {
            continue;
        }

        let Some(flow) = analysis.borrow_lifetime_flows.get(&did) else {
            continue;
        };
        let input_len = body.arg_count;
        let Some(returned_inputs) = returned_input_indexes(&flow.summary, input_len) else {
            continue;
        };

        let mut allocator =
            LifetimeNameAllocator::with_existing(existing_hir_lifetime_params(input.tcx, did));
        let lifetime = allocator.next();
        let mut input_lifetimes = vec![None; input_len];
        for input_index in returned_inputs {
            input_lifetimes[input_index] = Some(lifetime);
        }

        plans.insert(
            did,
            FnLifetimePlan {
                input_lifetimes,
                output_lifetime: Some(lifetime),
            },
        );
    }

    plans
}

fn returned_input_indexes(summary: &LifetimeFlowSummary, input_len: usize) -> Option<Vec<usize>> {
    let return_slot = summary
        .slots
        .iter_enumerated()
        .find_map(|(slot, sig_slot)| is_depth0_return_slot(*sig_slot).then_some(slot))?;
    let mut input_indexes = vec![];

    for (source, source_slot) in summary.slots.iter_enumerated() {
        if !summary.value_flows.contains(source, return_slot) {
            continue;
        }
        let Some(input_index) = depth0_arg_input_index(*source_slot, input_len) else {
            continue;
        };
        if !input_indexes.contains(&input_index) {
            input_indexes.push(input_index);
        }
    }

    if input_indexes.is_empty() {
        None
    } else {
        input_indexes.sort_unstable();
        Some(input_indexes)
    }
}

fn is_depth0_return_slot(slot: SignatureSlot) -> bool {
    slot.place.root == SignatureRoot::Return
        && slot.place.deref_depth == 0
        && slot.place.field.is_none()
        && slot.depth == 0
}

fn depth0_arg_input_index(slot: SignatureSlot, input_len: usize) -> Option<usize> {
    let SignatureRoot::Arg(local) = slot.place.root else {
        return None;
    };
    if slot.place.deref_depth != 0 || slot.place.field.is_some() || slot.depth != 0 {
        return None;
    }
    mir_arg_local_to_input_index(local).filter(|input_index| *input_index < input_len)
}

fn mir_arg_local_to_input_index(local: Local) -> Option<usize> {
    local.index().checked_sub(1)
}

fn struct_lifetime_plans(
    tcx: TyCtxt<'_>,
    analysis: &Analysis,
) -> FxHashMap<LocalDefId, StructLifetimePlan> {
    let mut fields_by_struct: FxHashMap<LocalDefId, Vec<StructFieldSlot>> = FxHashMap::default();
    for field in analysis
        .borrow_promotion_result
        .mutable_fields
        .iter()
        .chain(analysis.borrow_promotion_result.shared_fields.iter())
        .copied()
    {
        let fields = fields_by_struct.entry(field.struct_did).or_default();
        if !fields.contains(&field) {
            fields.push(field);
        }
    }

    let mut plans = FxHashMap::default();
    for (struct_did, mut fields) in fields_by_struct {
        fields.sort_by_key(|field| field.field_index);
        let mut allocator =
            LifetimeNameAllocator::with_existing(existing_hir_lifetime_params(tcx, struct_did));
        let mut plan = StructLifetimePlan::default();
        for field in fields {
            plan.field_lifetimes
                .insert(field.field_index, allocator.next());
        }
        plans.insert(struct_did, plan);
    }

    plans
}

#[cfg(test)]
mod tests {
    use rustc_index::{
        IndexVec,
        bit_set::{DenseBitSet, SparseBitMatrix},
    };

    use super::*;
    use crate::analyses::borrow::lifetime_flow::{LifetimeSlot, SignaturePlace};

    #[test]
    fn returned_input_indexes_keep_only_depth0_direct_arg_flows_to_return() {
        let mut slots: IndexVec<LifetimeSlot, SignatureSlot> = IndexVec::new();
        let direct_arg = slots.push(SignatureSlot {
            place: SignaturePlace {
                root: SignatureRoot::Arg(Local::from_u32(1)),
                deref_depth: 0,
                field: None,
            },
            depth: 0,
        });
        let deeper_arg = slots.push(SignatureSlot {
            place: SignaturePlace {
                root: SignatureRoot::Arg(Local::from_u32(2)),
                deref_depth: 0,
                field: None,
            },
            depth: 1,
        });
        let derefed_arg = slots.push(SignatureSlot {
            place: SignaturePlace {
                root: SignatureRoot::Arg(Local::from_u32(2)),
                deref_depth: 1,
                field: None,
            },
            depth: 0,
        });
        let out_of_range_arg = slots.push(SignatureSlot {
            place: SignaturePlace {
                root: SignatureRoot::Arg(Local::from_u32(4)),
                deref_depth: 0,
                field: None,
            },
            depth: 0,
        });
        let return_slot = slots.push(SignatureSlot {
            place: SignaturePlace {
                root: SignatureRoot::Return,
                deref_depth: 0,
                field: None,
            },
            depth: 0,
        });
        let mut value_flows = SparseBitMatrix::new(slots.len());
        value_flows.insert(direct_arg, return_slot);
        value_flows.insert(deeper_arg, return_slot);
        value_flows.insert(derefed_arg, return_slot);
        value_flows.insert(out_of_range_arg, return_slot);
        let slot_count = slots.len();
        let summary = LifetimeFlowSummary {
            slots,
            value_flows,
            storage_aliases: SparseBitMatrix::new(slot_count),
            unknown_targets: DenseBitSet::new_empty(slot_count),
        };

        assert_eq!(returned_input_indexes(&summary, 2), Some(vec![0]));
    }

    #[test]
    fn lifetime_name_allocator_skips_existing_lifetime_names() {
        ::utils::compilation::run_compiler_on_str("", |_tcx| {
            let mut allocator =
                LifetimeNameAllocator::with_existing([Symbol::intern("a"), Symbol::intern("b")]);

            assert_eq!(allocator.next(), Symbol::intern("c"));
        })
        .unwrap();
    }
}
