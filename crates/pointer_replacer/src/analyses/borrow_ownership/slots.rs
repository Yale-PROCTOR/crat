use std::ops::Range;

use rustc_hash::FxHashMap;
use rustc_index::IndexVec;
use rustc_middle::mir::Local;
use rustc_span::def_id::LocalDefId;

rustc_index::newtype_index! {
    #[orderable]
    // Debug-only label for this experiment's slot IDs. `BO_S(3)` means
    // borrow_ownership slot index 3; it has no semantic effect.
    #[debug_format = "BO_S({})"]
    pub struct SlotId {}
}

/// Pointer field in a global struct definition.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct StructFieldSlot {
    pub struct_did: LocalDefId,
    pub field_index: usize,
}

/// Owner of a flattened pointer slot.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum SlotOwner {
    Local(Local),
    Field(StructFieldSlot),
}

/// One pointer slot in a flattened local/field/deref path.
///
/// Depth 0 is the owner's own pointer value, and is the slot that decides the
/// owner's rewritten type. Depth k is the value reached after k dereferences.
/// The universe models deref chains only: struct-typed owners are handled at
/// universe-construction time by registering global field slots, not by
/// deepening local chains.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct Slot {
    pub owner: SlotOwner,
    pub depth: u8,
}

#[derive(Clone, Debug, Default)]
pub struct SlotUniverse {
    slots: IndexVec<SlotId, Slot>,
    owner_ranges: FxHashMap<SlotOwner, (SlotId, u8)>,
}

impl SlotUniverse {
    pub fn from_local_depths(local_depths: impl IntoIterator<Item = (Local, u8)>) -> Self {
        let mut universe = Self::default();
        for (local, depth_count) in local_depths {
            universe.register_local(local, depth_count);
        }

        universe
    }

    pub fn from_field_depths(
        field_depths: impl IntoIterator<Item = (StructFieldSlot, u8)>,
    ) -> Self {
        let mut universe = Self::default();
        for (field, depth_count) in field_depths {
            universe.register_field(field, depth_count);
        }

        universe
    }

    pub fn len(&self) -> usize {
        self.slots.len()
    }

    #[allow(dead_code)]
    pub fn is_empty(&self) -> bool {
        self.slots.is_empty()
    }

    pub fn slot(&self, slot: SlotId) -> &Slot {
        &self.slots[slot]
    }

    pub fn register_local(&mut self, local: Local, depth_count: u8) {
        self.register_owner(SlotOwner::Local(local), depth_count);
    }

    pub fn register_field(&mut self, field: StructFieldSlot, depth_count: u8) {
        self.register_owner(SlotOwner::Field(field), depth_count);
    }

    pub fn slots_for_local(&self, local: Local) -> Option<Range<SlotId>> {
        self.slots_for_owner(SlotOwner::Local(local))
    }

    pub fn slots_for_field(&self, field: StructFieldSlot) -> Option<Range<SlotId>> {
        self.slots_for_owner(SlotOwner::Field(field))
    }

    pub fn slot_for_local_depth(&self, local: Local, depth: u8) -> Option<SlotId> {
        self.slot_for_owner_depth(SlotOwner::Local(local), depth)
    }

    pub fn slot_for_field_depth(&self, field: StructFieldSlot, depth: u8) -> Option<SlotId> {
        self.slot_for_owner_depth(SlotOwner::Field(field), depth)
    }

    fn slot_for_owner_depth(&self, owner: SlotOwner, depth: u8) -> Option<SlotId> {
        self.owner_ranges
            .get(&owner)
            .and_then(|&(start, depth_count)| {
                (depth < depth_count).then(|| SlotId::from_usize(start.index() + depth as usize))
            })
    }

    fn slots_for_owner(&self, owner: SlotOwner) -> Option<Range<SlotId>> {
        self.owner_ranges.get(&owner).map(|&(start, depth_count)| {
            start..SlotId::from_usize(start.index() + depth_count as usize)
        })
    }

    fn register_owner(&mut self, owner: SlotOwner, depth_count: u8) {
        assert!(
            !self.owner_ranges.contains_key(&owner),
            "slot owner registered more than once: {owner:?}"
        );

        let start = SlotId::from_usize(self.slots.len());
        self.owner_ranges.insert(owner, (start, depth_count));
        push_depth_slots(&mut self.slots, owner, depth_count);
    }
}

fn push_depth_slots(slots: &mut IndexVec<SlotId, Slot>, owner: SlotOwner, depth_count: u8) {
    for depth in 0..depth_count {
        slots.push(Slot { owner, depth });
    }
}
