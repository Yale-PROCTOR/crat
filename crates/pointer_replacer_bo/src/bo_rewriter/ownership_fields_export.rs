//! Typed, in-memory R345 export contract. This is not a wire decoder or cache
//! schema. The future decoder must reject a partly absent record as Missing;
//! no required field has an Option/default. Proof bodies may live in exact,
//! typed companion records. Their digests and family tags are checked by the
//! adapter; interpreting those bodies remains the named producer's obligation.
use std::marker::PhantomData;

use super::emission::Kind;

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct Digest(pub [u8; 32]);
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct ProgramId(pub String);

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum EvidenceOwner {
    AcceptedModel,
    FrameQualification,
    NativeIdentity,
    #[allow(dead_code)]
    Emission,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Missing {
    pub owner: EvidenceOwner,
    pub reason: MissingReason,
}
pub type Evidence<T> = Result<T, Missing>;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum MissingReason {
    /// Exact contract field supplied by the decoder; no placeholder value.
    Field(&'static str),
    Frame(&'static str),
    Occurrence,
    Companion(FactFamily),
    ModelNotOwning(Kind),
    ModelInventory,
}

/// Bodies are addressed by both artifact digest and row, never by a display
/// name. A native decoder supplies the verified record inventory separately.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct RecordKey {
    pub artifact: Digest,
    pub row: u32,
}
pub trait FactTag {}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FactRef<T: FactTag> {
    pub record: RecordKey,
    marker: PhantomData<T>,
}
impl<T: FactTag> FactRef<T> {
    #[cfg(test)]
    pub fn new(record: RecordKey) -> Self {
        Self {
            record,
            marker: PhantomData,
        }
    }
}
macro_rules! families {
    ($($tag:ident),+ $(,)?) => {
        #[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
        pub enum FactFamily { $($tag),+ }
        $(#[derive(Clone, Debug, PartialEq, Eq)] #[allow(dead_code)] pub struct $tag;
          impl FactTag for $tag {})+
    }
}
families!(GenerationRecipe,);

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SourceFrame {
    L01DoublePrime,
}

// Lossless hold vocabulary from licensing at 5506aa42 (report 001 pin).
// Unknown future variants must be rejected by the decoder, never flattened.
