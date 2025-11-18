use core::{hash::Hash, ops::RangeBounds};

///
/// Range of [`usize`] that may have an unbounded endpoint, but always has a defined start.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub struct RangeAddressable {
    start: usize,
    end: Option<usize>,
}

impl RangeAddressable {
    ///
    /// Try to convert a generic [`RangeBounds`] into a [`RangeAddressable`].
    ///
    /// Returns `None` on `usize` overflow, or if the ending index is less than the starting index.
    pub fn try_from_bounds<RB: RangeBounds<usize>>(bounds: RB) -> Option<Self> {
        use core::ops::Bound::*;

        let start = match bounds.start_bound() {
            Unbounded => 0,
            Included(i) => *i,
            Excluded(i) => (*i).checked_add(1)?,
        };

        let end = match bounds.end_bound() {
            Excluded(i) if *i >= start => Some(*i),
            Included(i) if *i >= start => Some((*i).checked_add(1)?),
            Unbounded => None,
            _ => return None,
        };

        Some(RangeAddressable { start, end })
    }

    ///
    /// Starting index, inclusive. Represents the first element in the range.
    #[inline]
    pub fn start(&self) -> usize {
        self.start
    }

    ///
    /// Ending index, exclusive. If `None`, represents an unbounded upper range.
    ///
    /// If `Some(x)`, for any `RangeAddressable` `r`, it is guaranteed that `x >= r.start()`.
    #[inline]
    pub fn end(&self) -> Option<usize> {
        self.end
    }
}
