//! Transport of already established coordinate relations, not an evidence
//! producer. Integration must supply compiler identities backed by constructor,
//! copy and join transport, including the dynamic generation relation.
//! Copying these administrative handles never copies a slice capability.

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Hold {
    Origin,
    Layout,
    Window,
    Distance,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum SignCapture {
    Nonnegative,
    NegativeOrUnknown,
    Missing,
}

impl From<Option<bool>> for SignCapture {
    fn from(capture: Option<bool>) -> Self {
        match capture {
            Some(false) => Self::Nonnegative,
            Some(true) => Self::NegativeOrUnknown,
            None => Self::Missing,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct Coordinates<K> {
    pub origin: K,
    pub generation_relation: K,
    pub window_origin: K,
    pub element_type: K,
    pub element_size: usize,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct Position<K> {
    pub coordinates: Coordinates<K>,
    pub index: usize,
    pub length: usize,
}

impl<K: Eq> Position<K> {
    fn validate(&self) -> Result<(), Hold> {
        let bytes = self.length.checked_mul(self.coordinates.element_size);
        if self.coordinates.element_size == 0
            || bytes.is_none_or(|bytes| bytes > isize::MAX as usize)
        {
            return Err(Hold::Layout);
        }
        if self.index > self.length {
            return Err(Hold::Window);
        }
        Ok(())
    }

    /// Only administrative distance is checked here. Equality of relation keys
    /// is useful only after the decision collector proves their transport.
    pub(crate) fn difference(&self, other: &Self) -> Result<isize, Hold> {
        self.validate()?;
        other.validate()?;
        if self.coordinates != other.coordinates {
            return Err(Hold::Origin);
        }
        let left = isize::try_from(self.index).map_err(|_| Hold::Distance)?;
        let right = isize::try_from(other.index).map_err(|_| Hold::Distance)?;
        left.checked_sub(right).ok_or(Hold::Distance)
    }

    pub(crate) fn element_index(&self) -> Result<usize, Hold> {
        self.validate()?;
        if self.index < self.length {
            Ok(self.index)
        } else {
            Err(Hold::Window)
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum ExtentOrigin<K> {
    Evidence(K),
    Fallback { origin_receipt: K, site_receipt: K },
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct Extent<K> {
    pub elements: usize,
    pub origin: ExtentOrigin<K>,
}

impl<K: Copy> Extent<K> {
    /// The count has already been evaluated. A dependent construction receives
    /// its own receipt and retains the root of any fabricated extent.
    pub(crate) fn tail(self, index: usize, site_receipt: K) -> Result<Self, Hold> {
        let elements = self.elements.checked_sub(index).ok_or(Hold::Window)?;
        let origin = match self.origin {
            ExtentOrigin::Evidence(receipt) => ExtentOrigin::Evidence(receipt),
            ExtentOrigin::Fallback { origin_receipt, .. } => ExtentOrigin::Fallback {
                origin_receipt,
                site_receipt,
            },
        };
        Ok(Self { elements, origin })
    }
}
