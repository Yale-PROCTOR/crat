/// Rewritten kind for one flattened pointer slot.
///
/// This is the Rust-side semantic domain. Solver code should encode it with
/// one-hot booleans such as `raw(slot)`, `ref(slot)`, and `own(slot)`, then map
/// the model back to this enum.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum SlotKind {
    Raw,
    Ref,
    Owning,
}

impl SlotKind {
    pub const ALL: [Self; 3] = [Self::Raw, Self::Ref, Self::Owning];
}
