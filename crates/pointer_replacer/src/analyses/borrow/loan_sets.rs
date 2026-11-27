use std::{ops::Range, rc::Rc};

use itertools::Itertools as _;
use rustc_index::{Idx, IndexVec};
use rustc_mir_dataflow::{JoinSemiLattice, fmt::DebugWithContext};

use super::Loan;

/// Sorted, disjoint ranges of loan IDs. Loans issued together have consecutive IDs.
/// Sharing a row lets dataflow keep a snapshot without copying unchanged ranges.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct LoanSet(Option<Rc<Vec<Range<u32>>>>);

impl LoanSet {
    fn ranges(&self) -> &[Range<u32>] {
        self.0.as_deref().map_or(&[], Vec::as_slice)
    }

    pub fn is_empty(&self) -> bool {
        self.0.is_none()
    }

    pub fn iter(&self) -> impl Iterator<Item = Loan> + '_ {
        self.ranges().iter().cloned().flatten().map(Loan::from_u32)
    }

    pub fn contains(&self, loan: Loan) -> bool {
        let loan = loan.as_u32();
        let ranges = self.ranges();
        let index = ranges.partition_point(|range| range.end <= loan);
        ranges.get(index).is_some_and(|range| range.start <= loan)
    }

    pub fn insert(&mut self, loan: Loan) -> bool {
        let index = loan.as_u32();
        self.insert_range(index..index + 1)
    }

    fn insert_range(&mut self, mut range: Range<u32>) -> bool {
        let ranges = self.ranges();
        // Include adjacent ranges so the result stays canonical.
        let first = ranges.partition_point(|current| current.end < range.start);
        let last = ranges.partition_point(|current| current.start <= range.end);
        if first < last {
            if ranges[first].start <= range.start && range.end <= ranges[first].end {
                return false;
            }
            range.start = range.start.min(ranges[first].start);
            range.end = range.end.max(ranges[last - 1].end);
        }

        let ranges = Rc::make_mut(self.0.get_or_insert_with(|| Rc::new(Vec::new())));
        if first == last {
            ranges.insert(first, range);
        } else {
            ranges[first] = range;
            ranges.drain(first + 1..last);
        }
        true
    }

    pub fn remove(&mut self, loan: Loan) -> bool {
        let index = loan.as_u32();
        let range = index..index + 1;
        self.subtract_ranges(std::slice::from_ref(&range))
    }

    pub fn union(&mut self, other: &Self) -> bool {
        if other.is_empty() || self == other {
            return false;
        }
        if self.is_empty() {
            *self = other.clone();
            return true;
        }
        if let [range] = other.ranges() {
            return self.insert_range(range.clone());
        }
        let mut result: Vec<Range<u32>> = Vec::new();
        for range in self
            .ranges()
            .iter()
            .merge_by(other.ranges(), |left, right| left.start <= right.start)
        {
            if let Some(last) = result.last_mut()
                && range.start <= last.end
            {
                last.end = last.end.max(range.end);
            } else {
                result.push(range.clone());
            }
        }
        self.replace_ranges(result)
    }

    pub fn intersect(&mut self, other: &Self) {
        if self.is_empty() || self == other {
            return;
        }
        let mut result = Vec::new();
        let mut right = other.ranges();
        for left in self.ranges() {
            right = &right[right.partition_point(|range| range.end <= left.start)..];
            for range in right.iter().take_while(|range| range.start < left.end) {
                result.push(left.start.max(range.start)..left.end.min(range.end));
            }
        }
        self.replace_ranges(result);
    }

    pub fn subtract(&mut self, other: &Self) {
        self.subtract_ranges(other.ranges());
    }

    fn subtract_ranges(&mut self, mut right: &[Range<u32>]) -> bool {
        if self.is_empty() || right.is_empty() {
            return false;
        }
        let mut result = Vec::new();
        for left in self.ranges() {
            right = &right[right.partition_point(|range| range.end <= left.start)..];
            let mut start = left.start;
            for range in right.iter().take_while(|range| range.start < left.end) {
                if start < range.start {
                    result.push(start..range.start);
                }
                start = range.end;
            }
            if start < left.end {
                result.push(start..left.end);
            }
        }
        self.replace_ranges(result)
    }

    fn replace_ranges(&mut self, ranges: Vec<Range<u32>>) -> bool {
        if self.ranges() == ranges {
            return false;
        }
        self.0 = (!ranges.is_empty()).then(|| Rc::new(ranges));
        true
    }
}

impl JoinSemiLattice for LoanSet {
    fn join(&mut self, other: &Self) -> bool {
        self.union(other)
    }
}

impl<C> DebugWithContext<C> for LoanSet {}

#[derive(Clone)]
pub struct LoanRows<R: Idx>(IndexVec<R, Option<LoanSet>>);

impl<R: Idx> Default for LoanRows<R> {
    fn default() -> Self {
        Self(IndexVec::new())
    }
}

impl<R: Idx> LoanRows<R> {
    pub fn row(&self, row: R) -> Option<&LoanSet> {
        self.0.get(row)?.as_ref()
    }

    pub fn rows(&self) -> impl Iterator<Item = R> {
        self.0.indices()
    }

    pub fn contains(&self, row: R, loan: Loan) -> bool {
        self.row(row).is_some_and(|loans| loans.contains(loan))
    }

    pub fn insert(&mut self, row: R, loan: Loan) {
        self.0
            .get_or_insert_with(row, LoanSet::default)
            .insert(loan);
    }

    pub fn remove(&mut self, row: R, loan: Loan) {
        if let Some(Some(loans)) = self.0.get_mut(row) {
            loans.remove(loan);
        }
    }

    pub fn set_row(&mut self, row: R, loans: LoanSet) {
        *self.0.get_or_insert_with(row, LoanSet::default) = loans;
    }
}

#[cfg(test)]
mod tests {
    use rustc_index::bit_set::DenseBitSet;

    use super::*;

    #[test]
    fn range_operations_match_dense_bits() {
        let indices = [0, 1, 2, 3, 63, 64, 65, 4095].map(Loan::from_u32);
        let sets: Vec<_> = (0..1 << indices.len())
            .map(|mask| {
                let mut ranges = LoanSet::default();
                let mut dense = DenseBitSet::new_empty(4096);
                for (index, &loan) in indices.iter().enumerate().rev() {
                    if mask & (1 << index) != 0 {
                        assert!(ranges.insert(loan));
                        assert!(!ranges.insert(loan));
                        dense.insert(loan);
                    }
                }
                (ranges, dense)
            })
            .collect();
        for (left, dense_left) in &sets {
            for (right, dense_right) in &sets {
                let mut ranges = left.clone();
                let mut dense = dense_left.clone();
                assert_eq!(ranges.join(right), dense.union(dense_right));
                assert!(ranges.iter().eq(dense.iter()));
                let mut ranges = left.clone();
                let mut dense = dense_left.clone();
                ranges.intersect(right);
                dense.intersect(dense_right);
                assert!(ranges.iter().eq(dense.iter()));
                let mut ranges = left.clone();
                let mut dense = dense_left.clone();
                ranges.subtract(right);
                dense.subtract(dense_right);
                assert!(ranges.iter().eq(dense.iter()));
            }
            assert!(left.iter().eq(dense_left.iter()));
        }
    }
}
