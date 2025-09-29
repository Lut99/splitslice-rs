//  SLICE.rs
//    by Lut99
//
//  Description:
//!   Implements the slice half of the library.
//

use std::cmp::Ordering;
use std::fmt::{Debug, Formatter, Result as FResult};
use std::hash::{Hash, Hasher};
use std::iter::FusedIterator;
use std::ops::Index;

use crate::str::SplitStr;


/***** ITERATORS *****/
/// By-reference iterator for the [`SplitSlice`].
#[derive(Debug)]
pub struct Iter<'a, const N: usize, T> {
    /// The slice to iterator over.
    slice: SplitSlice<'a, N, T>,
    /// Front index, as an (inclusive) slice, index-in-slice pair.
    front: (usize, usize),
    /// Back index, as an (exclusive) slice, index-in-slice pair.
    back:  (usize, usize),
}

// Constructors (private)
impl<'a, const N: usize, T> Iter<'a, N, T> {
    #[inline]
    const fn new(slice: SplitSlice<'a, N, T>) -> Self { Self { slice, front: (0, 0), back: (N, if N > 0 { slice.0[N - 1].len() } else { 0 }) } }
}

// Ops
impl<'a, const N: usize, T> Clone for Iter<'a, N, T> {
    #[inline]
    fn clone(&self) -> Self { Self { slice: self.slice, front: self.front, back: self.back } }
}
impl<'a, const N: usize, T> Copy for Iter<'a, N, T> {}

// Iterator
impl<'a, const N: usize, T> DoubleEndedIterator for Iter<'a, N, T> {
    #[inline]
    fn next_back(&mut self) -> Option<Self::Item> {
        // Step 1: we ignore the front by simply requiring that back is after it
        if self.front.0 >= self.back.0 || (self.back.0 > 0 && self.front.0 == self.back.0 - 1 && self.front.1 >= self.back.1) {
            return None;
        }

        // Step 2: Try to find a slice for which we're in range
        while self.back.0 > 0 {
            let Some(slice) = self.slice.0.get(self.back.0 - 1) else { unreachable!() };

            // If `i` is within range of this slice, return it; else, try the next slice
            if self.back.1 > 0 {
                self.back.1 -= 1;
                return Some(slice.get(self.back.1).unwrap_or_else(|| unreachable!()));
            } else {
                // Simply try again on the next slice
                self.back.0 -= 1;
                self.back.1 = if self.back.0 > 0 { self.slice.0.get(self.back.0 - 1).copied().map(<[T]>::len).unwrap_or(0) } else { 0 };
            }
        }
        None
    }
}
impl<'a, const N: usize, T> ExactSizeIterator for Iter<'a, N, T> {
    #[inline]
    fn len(&self) -> usize {
        // First, let's see how many slices are touched
        let n_slices: usize = self.back.0.saturating_sub(self.front.0);
        if n_slices == 1 {
            // Special case: one slice is touched. The remaining length is just the difference
            // within this slice!
            return std::cmp::min(self.back.1.saturating_sub(self.front.1), self.slice.0.get(self.front.0).copied().map(<[T]>::len).unwrap_or(0));
        } else if n_slices == 0 {
            // Special case: nothing is touched, ez
            return 0;
        }

        // No choice but to count the remaining indices
        let mut rem: usize = 0;
        for (i, &slice) in self.slice.0[self.front.0..self.back.0].iter().enumerate() {
            if i == 0 {
                // First one (respect the index in that slice)
                rem += slice.len().saturating_sub(self.front.1);
            } else if self.back.0 > 0 && self.front.0 + i == self.back.0 - 1 {
                // Last one (respect the index in that slice)
                rem += self.back.1;
            } else {
                // Middle ones (can get the full slice)
                rem += slice.len();
            }
        }
        rem
    }
}
impl<'a, const N: usize, T> FusedIterator for Iter<'a, N, T> {}
impl<'a, const N: usize, T> Iterator for Iter<'a, N, T> {
    type Item = &'a T;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        // Step 1: we ignore the back by simply requiring that front is before it
        if self.front.0 >= self.back.0 || (self.back.0 > 0 && self.front.0 == self.back.0 - 1 && self.front.1 >= self.back.1) {
            return None;
        }

        // Step 2: Try to find a slice for which we're in range
        while let Some(slice) = self.slice.0.get(self.front.0) {
            // If `i` is within range of this slice, return it; else, try the next slice
            if let Some(elem) = slice.get(self.front.1) {
                self.front.1 += 1;
                return Some(elem);
            } else {
                // Simply try again on the next slice
                self.front.0 += 1;
                self.front.1 = 0;
            }
        }
        None
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        let len: usize = self.len();
        (len, Some(len))
    }
}





/***** LIBRARY *****/
/// A small datastructure for pretending a (statically determined) list of slices are one slice.
///
/// This does not mean that their memory becomes contiguous; instead, the SplitSlice will implement
/// operations as if they are.
pub struct SplitSlice<'a, const N: usize, T>(pub [&'a [T]; N]);

// Constructors
impl<const N: usize, T> SplitSlice<'static, N, T> {
    /// Creates a new SplitSlice with only empty slices.
    ///
    /// # Returns
    /// A new SplitSlice that contains only empty slices.
    #[inline]
    pub const fn empty() -> Self { Self([&[]; N]) }
}
impl<'a, const N: usize, T> SplitSlice<'a, N, T> {
    /// Creates a new SplitSlice out of the given list of slices.
    ///
    /// # Arguments
    /// - `slices`: The list of slices out of which to built this SplitSlice.
    ///
    /// # Returns
    /// A new SplitSlice that contains all of them.
    #[inline]
    pub const fn new(slices: [&'a [T]; N]) -> Self { Self(slices) }
}

// Formatters
impl<'a, const N: usize, T: Debug> Debug for SplitSlice<'a, N, T> {
    #[inline]
    fn fmt(&self, f: &mut Formatter<'_>) -> FResult {
        let mut fmt = f.debug_list();
        for slice in self.0 {
            fmt.entries(slice);
        }
        fmt.finish()
    }
}

// Ops
impl<'a, const N: usize, T> Copy for SplitSlice<'a, N, T> {}
impl<'a, const N: usize, T> Clone for SplitSlice<'a, N, T> {
    #[inline]
    fn clone(&self) -> Self { Self(self.0) }
}
impl<'a, const N: usize, T: Eq> Eq for SplitSlice<'a, N, T> {}
impl<'a, const N: usize, T: Hash> Hash for SplitSlice<'a, N, T> {
    #[inline]
    fn hash<H: Hasher>(&self, state: &mut H) {
        for elem in self.iter() {
            elem.hash(state);
        }
    }
}
impl<'a, 'a2, const N: usize, const N2: usize, T: PartialEq<T2>, T2> PartialEq<SplitSlice<'a2, N2, T2>> for SplitSlice<'a, N, T> {
    #[inline]
    fn eq(&self, other: &SplitSlice<'a2, N2, T2>) -> bool {
        let mut iter1 = self.iter();
        let mut iter2 = other.iter();
        loop {
            match (iter1.next(), iter2.next()) {
                (Some(lhs), Some(rhs)) if !lhs.eq(rhs) => return false,
                (Some(_), Some(_)) => continue,
                (None, None) => return true,
                _ => return false,
            }
        }
    }

    #[inline]
    fn ne(&self, other: &SplitSlice<'a2, N2, T2>) -> bool {
        let mut iter1 = self.iter();
        let mut iter2 = other.iter();
        loop {
            match (iter1.next(), iter2.next()) {
                (Some(lhs), Some(rhs)) if lhs.ne(rhs) => return true,
                (Some(_), Some(_)) => continue,
                (None, None) => return false,
                _ => return true,
            }
        }
    }
}
impl<'a, const N: usize, T: Ord> Ord for SplitSlice<'a, N, T> {
    #[inline]
    fn cmp(&self, other: &Self) -> Ordering {
        let mut iter1 = self.iter();
        let mut iter2 = other.iter();
        loop {
            match (iter1.next(), iter2.next()) {
                (Some(lhs), Some(rhs)) => {
                    let cmp = lhs.cmp(rhs);
                    if cmp != Ordering::Equal {
                        return cmp;
                    }
                },
                (Some(_), None) => return Ordering::Greater,
                (None, Some(_)) => return Ordering::Less,
                (None, None) => return Ordering::Equal,
            }
        }
    }
}
impl<'a, const N: usize, T: PartialOrd> PartialOrd for SplitSlice<'a, N, T> {
    #[inline]
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        let mut iter1 = self.iter();
        let mut iter2 = other.iter();
        loop {
            match (iter1.next(), iter2.next()) {
                (Some(lhs), Some(rhs)) => {
                    let cmp = lhs.partial_cmp(rhs)?;
                    if cmp != Ordering::Equal {
                        return Some(cmp);
                    }
                },
                (Some(_), None) => return Some(Ordering::Greater),
                (None, Some(_)) => return Some(Ordering::Less),
                (None, None) => return Some(Ordering::Equal),
            }
        }
    }
}

// Indexing
impl<'a, const N: usize, T> SplitSlice<'a, N, T> {
    /// Returns the element at the given index.
    ///
    /// Note: no `get_unchecked()` exists for this slice because we always need to search through
    /// slices to find which one contains the given index. Hence, this operation is not as free as
    /// normal slice indexing.
    ///
    /// # Arguments
    /// - `index`: The (zero-indexed) position of the element to get.
    ///
    /// # Returns
    /// If the `index` was in bounds, returns the element. Else, [`None`] is returned.
    #[inline]
    pub const fn get(&self, mut index: usize) -> Option<&'a T> {
        // NOTE: Awkward iteration and indexing, but now it's `const`
        let mut i: usize = 0;
        while i < N {
            let slice: &'a [T] = self.0[i];
            if index < slice.len() {
                return Some(&slice[index]);
            }
            index -= self.0[i].len();
            i += 1;
        }
        None
    }
}
impl<'a, const N: usize, T> Index<usize> for SplitSlice<'a, N, T> {
    type Output = T;

    #[inline]
    fn index(&self, index: usize) -> &T {
        self.get(index).unwrap_or_else(|| panic!("Index {index} is out-of-bounds for SplitSlice of length {}", self.len()))
    }
}

// Slice
impl<'a, const N: usize, T: Clone> SplitSlice<'a, N, T> {
    /// Turns this `SplitSlice` into a [`Vec`].
    ///
    /// # Returns
    /// An owned, contiguous slice of memory with a clone of the contents in the SplitSlice.
    #[inline]
    pub fn to_vec(&self) -> Vec<T> {
        let mut res = Vec::with_capacity(self.len());
        for elem in self.iter() {
            res.push(elem.clone());
        }
        res
    }
}
impl<'a, const N: usize, T> SplitSlice<'a, N, T> {
    /// Returns the number of elements in the SplitSlice.
    ///
    /// # Returns
    /// A number representing the total length of all internal slice parts.
    #[inline]
    pub const fn len(&self) -> usize {
        // NOTE: Bit awkward iteration to keep `const`
        let mut i: usize = 0;
        let mut len: usize = 0;
        while i < N {
            len += self.0[i].len();
            i += 1;
        }
        len
    }

    /// Alias for checking if [`SplitSlice::len()`] is empty.
    ///
    /// # Returns
    /// True if `SplitSlice::len() == 0`, false otherwise.
    #[inline]
    pub const fn is_empty(&self) -> bool { self.len() == 0 }
}
impl<'a, const N: usize> SplitSlice<'a, N, u8> {
    /// Returns this SplitSlice as a [`SplitStr`].
    ///
    /// Note that the _whole_ byte is assumed to be a string; i.e., codepoints are allowed to cross
    /// slice boundaries.
    ///
    /// # Returns
    /// A [`SplitStr`] that owns this datastructure but such that it is assumed that it's valid
    /// UTF-8.
    ///
    /// # Errors
    /// This function returns an error if this was not valid UTF-8.
    #[inline]
    pub fn as_str(&self) -> Result<SplitStr<'a, N>, std::str::Utf8Error> { SplitStr::try_from(*self) }
}

// Iterators
impl<'a, const N: usize, T> SplitSlice<'a, N, T> {
    /// Returns an iterator yielding all elements in this slice by reference, in-order.
    ///
    /// # Returns
    /// An [`Iter`] that will yield `&T`.
    #[inline]
    pub const fn iter(&self) -> Iter<'a, N, T> { Iter::new(*self) }

    /// Special iterator yielding all of the internal slices.
    ///
    /// This is the only way to get contiguous memory out of the SplitSlice.
    ///
    /// # Returns
    /// An [`Iterator`] that will yield `&[T]`.
    #[inline]
    pub fn slices(&self) -> std::slice::Iter<'_, &'a [T]> { self.0.iter() }
}
impl<'a, const N: usize, T> IntoIterator for SplitSlice<'a, N, T> {
    type Item = &'a T;
    type IntoIter = Iter<'a, N, T>;

    #[inline]
    fn into_iter(self) -> Self::IntoIter { self.iter() }
}





/***** TESTS *****/
#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_split_slice_iter() {
        // Get an iterator
        let lhs = &[1, 2, 3];
        let rhs = &[4, 5, 6];
        let both = SplitSlice([lhs, rhs]);
        let mut iter = both.iter();
        assert_eq!(iter.len(), 6);
        assert_eq!(iter.next(), Some(&1));
        assert_eq!(iter.len(), 5);
        assert_eq!(iter.next(), Some(&2));
        assert_eq!(iter.len(), 4);
        assert_eq!(iter.next(), Some(&3));
        assert_eq!(iter.len(), 3);
        assert_eq!(iter.next(), Some(&4));
        assert_eq!(iter.len(), 2);
        assert_eq!(iter.next(), Some(&5));
        assert_eq!(iter.len(), 1);
        assert_eq!(iter.next(), Some(&6));
        assert_eq!(iter.len(), 0);
        assert_eq!(iter.next(), None);
        assert_eq!(iter.len(), 0);
        assert_eq!(iter.next(), None);
    }

    #[test]
    fn test_split_slice_iter_back() {
        // Get an iterator
        let lhs = &[1, 2, 3];
        let rhs = &[4, 5, 6];
        let both = SplitSlice([lhs, rhs]);
        let mut iter = both.iter();
        assert_eq!(iter.len(), 6);
        assert_eq!(iter.next_back(), Some(&6));
        assert_eq!(iter.len(), 5);
        assert_eq!(iter.next_back(), Some(&5));
        assert_eq!(iter.len(), 4);
        assert_eq!(iter.next_back(), Some(&4));
        assert_eq!(iter.len(), 3);
        assert_eq!(iter.next_back(), Some(&3));
        assert_eq!(iter.len(), 2);
        assert_eq!(iter.next_back(), Some(&2));
        assert_eq!(iter.len(), 1);
        assert_eq!(iter.next_back(), Some(&1));
        assert_eq!(iter.len(), 0);
        assert_eq!(iter.next_back(), None);
        assert_eq!(iter.len(), 0);
        assert_eq!(iter.next_back(), None);
    }

    #[test]
    fn test_split_slice_iter_both() {
        // Get an iterator
        let lhs = &[1, 2, 3];
        let rhs = &[4, 5, 6];
        let both = SplitSlice([lhs, rhs]);
        let mut iter = both.iter();
        assert_eq!(iter.len(), 6);
        assert_eq!(iter.next(), Some(&1));
        assert_eq!(iter.len(), 5);
        assert_eq!(iter.next(), Some(&2));
        assert_eq!(iter.len(), 4);
        assert_eq!(iter.next(), Some(&3));
        assert_eq!(iter.len(), 3);
        assert_eq!(iter.next_back(), Some(&6));
        assert_eq!(iter.len(), 2);
        assert_eq!(iter.next_back(), Some(&5));
        assert_eq!(iter.len(), 1);
        assert_eq!(iter.next(), Some(&4));
        assert_eq!(iter.len(), 0);
        assert_eq!(iter.next(), None);
        assert_eq!(iter.len(), 0);
        assert_eq!(iter.next_back(), None);
    }
}
