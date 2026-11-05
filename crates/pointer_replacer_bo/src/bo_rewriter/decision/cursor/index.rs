//! Arithmetic on administrative cursor indices, never on pointee storage.

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum IndexOp {
    Offset(isize),
    Add(usize),
    Sub(usize),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum IndexError {
    OutsideWindow,
    Overflow,
}

impl IndexOp {
    pub(crate) fn apply(self, index: usize, length: usize) -> Result<usize, IndexError> {
        if index > length {
            return Err(IndexError::OutsideWindow);
        }
        let next = match self {
            Self::Offset(delta) => index.checked_add_signed(delta),
            Self::Add(count) => index.checked_add(count),
            Self::Sub(count) => index.checked_sub(count),
        }
        .ok_or(IndexError::Overflow)?;
        if next > length {
            return Err(IndexError::OutsideWindow);
        }
        Ok(next)
    }
}
