//  STR.rs
//    by Lut99
//
//  Description:
//!   Implements the string half of the library.
//

use std::fmt::{Debug, Display, Formatter, Result as FResult};
use std::iter::FusedIterator;
use std::ops::Deref;

pub use crate::slice::Iter;
use crate::slice::SplitSlice;


/***** ITERATORS *****/
/// Iterator for [`SplitStr`] that is yielding [`char`]acters.
#[derive(Clone, Copy, Debug)]
pub struct Chars<'a, const N: usize> {
    /// The iterator yielding all bytes in the original iterator.
    bytes: Iter<'a, N, u8>,
}

// Constructors
impl<'a, const N: usize> Chars<'a, N> {
    #[inline]
    const fn new(slice: SplitSlice<'a, N, u8>) -> Self { Self { bytes: slice.iter() } }
}

// Iterators
impl<'a, const N: usize> DoubleEndedIterator for Chars<'a, N> {
    #[inline]
    fn next_back(&mut self) -> Option<Self::Item> {
        // A buffer that will at most contain a character
        let mut buffer: [u8; 4] = [0; 4];
        let mut buffer_len: usize = 0;
        while buffer_len < 4 {
            // Always the rest back to put it in the proper order
            for i in 0..buffer_len {
                buffer[buffer_len - i] = buffer[buffer_len - 1 - i];
            }
            buffer[0] = *self.bytes.next_back()?;
            buffer_len += 1;

            // Then check if this is still a unicode codepoint
            match std::str::from_utf8(&buffer[..buffer_len]) {
                // We found a valid char
                Ok(c) => {
                    let mut chars = c.chars();
                    let c: char = chars.next().unwrap_or_else(|| unreachable!());
                    #[cfg(debug_assertions)]
                    assert!(chars.next().is_none());
                    return Some(c);
                },
                // On its own, this doesn't make sense. Maybe adding more bytes will?
                Err(_) => continue,
            }
        }

        // This should never happen! The string is invalid UTF-8!!
        unreachable!()
    }
}
impl<'a, const N: usize> Iterator for Chars<'a, N> {
    type Item = char;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        // A buffer that will at most contain a character
        let mut buffer: [u8; 4] = [0; 4];
        let mut buffer_len: usize = 0;
        while buffer_len < 4 {
            buffer[buffer_len] = *self.bytes.next()?;
            buffer_len += 1;
            match std::str::from_utf8(&buffer[..buffer_len]) {
                // We found a valid char
                Ok(c) => {
                    let mut chars = c.chars();
                    let c: char = chars.next().unwrap_or_else(|| unreachable!());
                    #[cfg(debug_assertions)]
                    assert!(chars.next().is_none());
                    return Some(c);
                },
                // We need more bytes first before it's a char.
                Err(err) if err.error_len().is_none() => continue,
                // This should never happen! The string is invalid UTF-8!!
                Err(_) => unreachable!(),
            }
        }

        // This should never happen! The string is invalid UTF-8!!
        unreachable!()
    }
}
impl<'a, const N: usize> FusedIterator for Chars<'a, N> {}



/// Iterator for [`SplitStr`] that is yielding [`char`]acters with their indices.
#[derive(Clone, Copy, Debug)]
pub struct CharIndices<'a, const N: usize> {
    /// The iterator yielding all bytes in the original iterator.
    bytes: Iter<'a, N, u8>,
    /// Total count of bytes from the front.
    front: usize,
    /// Total count of bytes at the end.
    back:  usize,
}

// Constructors
impl<'a, const N: usize> CharIndices<'a, N> {
    #[inline]
    const fn new(slice: SplitSlice<'a, N, u8>) -> Self { Self { bytes: slice.iter(), front: 0, back: slice.len() } }
}

// Iterators
impl<'a, const N: usize> DoubleEndedIterator for CharIndices<'a, N> {
    #[inline]
    fn next_back(&mut self) -> Option<Self::Item> {
        // A buffer that will at most contain a character
        let mut buffer: [u8; 4] = [0; 4];
        let mut buffer_len: usize = 0;
        while buffer_len < 4 {
            // Always the rest back to put it in the proper order
            for i in 0..buffer_len {
                buffer[buffer_len - i] = buffer[buffer_len - 1 - i];
            }
            buffer[0] = *self.bytes.next_back()?;
            buffer_len += 1;
            self.back -= 1;

            // Then check if this is still a unicode codepoint
            match std::str::from_utf8(&buffer[..buffer_len]) {
                // We found a valid char
                Ok(c) => {
                    let mut chars = c.chars();
                    let c: char = chars.next().unwrap_or_else(|| unreachable!());
                    #[cfg(debug_assertions)]
                    assert!(chars.next().is_none());
                    return Some((self.back, c));
                },
                // On its own, this doesn't make sense. Maybe adding more bytes will?
                Err(_) => continue,
            }
        }

        // This should never happen! The string is invalid UTF-8!!
        unreachable!()
    }
}
impl<'a, const N: usize> Iterator for CharIndices<'a, N> {
    type Item = (usize, char);

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        // A buffer that will at most contain a character
        let mut buffer: [u8; 4] = [0; 4];
        let mut buffer_len: usize = 0;
        while buffer_len < 4 {
            buffer[buffer_len] = *self.bytes.next()?;
            buffer_len += 1;
            self.front += 1;
            match std::str::from_utf8(&buffer[..buffer_len]) {
                // We found a valid char
                Ok(c) => {
                    let mut chars = c.chars();
                    let c: char = chars.next().unwrap_or_else(|| unreachable!());
                    #[cfg(debug_assertions)]
                    assert!(chars.next().is_none());
                    return Some((self.front - buffer_len, c));
                },
                // We need more bytes first before it's a char.
                Err(err) if err.error_len().is_none() => continue,
                // This should never happen! The string is invalid UTF-8!!
                Err(_) => unreachable!(),
            }
        }

        // This should never happen! The string is invalid UTF-8!!
        unreachable!()
    }
}
impl<'a, const N: usize> FusedIterator for CharIndices<'a, N> {}





/***** LIBRARY *****/
#[derive(Clone, Copy, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct SplitStr<'a, const N: usize>(SplitSlice<'a, N, u8>);

// Constructors
impl<const N: usize> SplitStr<'static, N> {
    /// Creates a new SplitStr with only empty slices.
    ///
    /// # Returns
    /// A new SplitStr that contains only empty slices.
    #[inline]
    pub const fn empty() -> Self { Self(SplitSlice::empty()) }
}
impl<'a, const N: usize> SplitStr<'a, N> {
    /// Creates a new SplitStr out of the given list of strings.
    ///
    /// NOTE: This function isn't constant until
    /// [`MaybeUninit::array_assume_init()`](https://doc.rust-lang.org/std/mem/union.MaybeUninit.html#method.array_assume_init)
    /// lands... :(
    ///
    /// # Arguments
    /// - `strs`: The list of strs out of which to built this SplitStr.
    ///
    /// # Returns
    /// A new SplitStr that contains all of them.
    #[inline]
    pub fn new(strs: [&'a str; N]) -> Self {
        // Once the func lands, check
        // https://doc.rust-lang.org/std/mem/union.MaybeUninit.html#initializing-an-array-element-by-element

        // Until then, we use map
        Self(SplitSlice(strs.map(str::as_bytes)))
    }
}

// Formatters
impl<'a, const N: usize> Debug for SplitStr<'a, N> {
    #[inline]
    fn fmt(&self, f: &mut Formatter<'_>) -> FResult {
        // Serialize the string as a whole
        // We must do it this inefficiently, because the boundary of unicode points may be crossing
        // chunk boundaries.
        let all = self.0.to_vec();
        // SAFETY: We can unwrap because this struct can only be created with valid UTF-8 sequences.
        <String as Debug>::fmt(&unsafe { String::from_utf8_unchecked(all) }, f)
    }
}
impl<'a, const N: usize> Display for SplitStr<'a, N> {
    #[inline]
    fn fmt(&self, f: &mut Formatter<'_>) -> FResult {
        // Serialize the string as a whole
        // We must do it this inefficiently, because the boundary of unicode points may be crossing
        // chunk boundaries.
        let all = self.0.to_vec();
        // SAFETY: We can unwrap because this struct can only be created with valid UTF-8 sequences.
        <String as Display>::fmt(&unsafe { String::from_utf8_unchecked(all) }, f)
    }
}

// Strings
impl<'a, const N: usize> SplitStr<'a, N> {
    /// Turns this `SplitStr` into a [`String`].
    ///
    /// # Returns
    /// An owned, contiguous slice of memory with a clone of the contents in the SplitStr.
    #[inline]
    pub fn to_string(&self) -> String {
        let mut res = String::with_capacity(self.len());
        for slice in self.0.0 {
            // SAFETY: The `SplitStr` only contains valid UTF-8 strings
            res.push_str(unsafe { std::str::from_utf8_unchecked(slice) });
        }
        res
    }
}

// Iterators
impl<'a, const N: usize> SplitStr<'a, N> {
    /// Returns an iterator over the characters in the string.
    ///
    /// # Returns
    /// An iterator that will yield Unicode codepoints as [`char`]s.
    #[inline]
    pub const fn chars(&self) -> Chars<'a, N> { Chars::new(self.0) }

    /// Returns an iterator over the characters in the string with their corresponding byte
    /// positions.
    ///
    /// # Returns
    /// An iterator that will yield Unicode codepoints as [`char`]s.
    #[inline]
    pub const fn char_indices(&self) -> CharIndices<'a, N> { CharIndices::new(self.0) }
}

// Conversion
impl<'a, const N: usize> Deref for SplitStr<'a, N> {
    type Target = SplitSlice<'a, N, u8>;

    #[inline]
    fn deref(&self) -> &Self::Target { &self.0 }
}
impl<'a, const N: usize> TryFrom<SplitSlice<'a, N, u8>> for SplitStr<'a, N> {
    type Error = std::str::Utf8Error;

    #[inline]
    fn try_from(value: SplitSlice<'a, N, u8>) -> Result<Self, Self::Error> {
        // https://doc.rust-lang.org/std/str/struct.Utf8Error.html
        let mut buffer: [u8; 4] = [0; 4];
        let mut buffer_len: usize = 0;
        for slice in &value.0 {
            let mut slice: &[u8] = *slice;

            // If there is a buffer, use the first bytes to try and complete the codepoint
            if buffer_len > 0 {
                for i in 0..4 - buffer_len {
                    // Set the byte
                    buffer[buffer_len + i] = slice[i];
                    // Attempt to read the codepoint
                    match std::str::from_utf8(&buffer[..buffer_len + i]) {
                        Ok(_) => {
                            // It checks out; from here we continue as usual
                            buffer_len = 0;
                            slice = &slice[i..];
                            break;
                        },
                        Err(err) => {
                            if err.error_len().is_none() {
                                // We'll have to re-try with a bigger fish
                                continue;
                            }
                            return Err(err);
                        },
                    }
                }
            }

            // Try to verify this slice
            match std::str::from_utf8(slice) {
                Ok(_) => continue,
                Err(err) => {
                    if err.error_len().is_none() {
                        // It was unfinished. We remember the initial chunk that was valid...
                        let valid_up_to: usize = err.valid_up_to();
                        buffer_len = slice.len() - valid_up_to;
                        buffer[..buffer_len].copy_from_slice(&slice[valid_up_to..]);

                        // Then try with the next one
                        continue;
                    }
                    return Err(err);
                },
            }
        }

        // The slices check out. Return ourselves!
        Ok(Self(value))
    }
}





/***** TESTS *****/
#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_try_from_slice() {
        assert_eq!(SplitStr::try_from(SplitSlice([])), Ok(SplitStr::empty()));
        assert_eq!(format!("{:?}", SplitStr::try_from(SplitSlice([b"Hello, world!"]))), "Ok(\"Hello, world!\")");
        assert_eq!(format!("{:?}", SplitStr::try_from(SplitSlice([b"Hello, ", b"world!"]))), "Ok(\"Hello, world!\")");
        assert_eq!(
            format!(
                "{:?}",
                SplitStr::try_from(SplitSlice([&[0x48, 0x65, 0x6C, 0x6C, 0x6F, 0x2C, 0x20, 0x77], &[0xC3, 0xBF, 0x72, 0x6C, 0x64, 0x21]]))
            ),
            "Ok(\"Hello, wÿrld!\")"
        );
        assert_eq!(
            format!(
                "{:?}",
                SplitStr::try_from(SplitSlice([&[0x48, 0x65, 0x6C, 0x6C, 0x6F, 0x2C, 0x20, 0xFF], &[0xC3, 0xBF, 0x72, 0x6C, 0x64, 0x21]]))
            ),
            "Err(Utf8Error { valid_up_to: 7, error_len: Some(1) })"
        );
    }

    #[test]
    fn test_chars() {
        let strs = SplitStr::new(["Hello, ", "world!"]);
        let mut chars = strs.chars();
        assert_eq!(chars.next(), Some('H'));
        assert_eq!(chars.next(), Some('e'));
        assert_eq!(chars.next(), Some('l'));
        assert_eq!(chars.next(), Some('l'));
        assert_eq!(chars.next(), Some('o'));
        assert_eq!(chars.next(), Some(','));
        assert_eq!(chars.next(), Some(' '));
        assert_eq!(chars.next(), Some('w'));
        assert_eq!(chars.next(), Some('o'));
        assert_eq!(chars.next(), Some('r'));
        assert_eq!(chars.next(), Some('l'));
        assert_eq!(chars.next(), Some('d'));
        assert_eq!(chars.next(), Some('!'));
        assert_eq!(chars.next(), None);
        assert_eq!(chars.next(), None);

        let strs = SplitStr::new(["Hello, ", "wÿrld!"]);
        let mut chars = strs.chars();
        assert_eq!(chars.next(), Some('H'));
        assert_eq!(chars.next(), Some('e'));
        assert_eq!(chars.next(), Some('l'));
        assert_eq!(chars.next(), Some('l'));
        assert_eq!(chars.next(), Some('o'));
        assert_eq!(chars.next(), Some(','));
        assert_eq!(chars.next(), Some(' '));
        assert_eq!(chars.next(), Some('w'));
        assert_eq!(chars.next(), Some('ÿ'));
        assert_eq!(chars.next(), Some('r'));
        assert_eq!(chars.next(), Some('l'));
        assert_eq!(chars.next(), Some('d'));
        assert_eq!(chars.next(), Some('!'));
        assert_eq!(chars.next(), None);
        assert_eq!(chars.next(), None);
    }

    #[test]
    fn test_chars_back() {
        let strs = SplitStr::new(["Hello, ", "world!"]);
        let mut chars = strs.chars();
        assert_eq!(chars.next_back(), Some('!'));
        assert_eq!(chars.next_back(), Some('d'));
        assert_eq!(chars.next_back(), Some('l'));
        assert_eq!(chars.next_back(), Some('r'));
        assert_eq!(chars.next_back(), Some('o'));
        assert_eq!(chars.next_back(), Some('w'));
        assert_eq!(chars.next_back(), Some(' '));
        assert_eq!(chars.next_back(), Some(','));
        assert_eq!(chars.next_back(), Some('o'));
        assert_eq!(chars.next_back(), Some('l'));
        assert_eq!(chars.next_back(), Some('l'));
        assert_eq!(chars.next_back(), Some('e'));
        assert_eq!(chars.next_back(), Some('H'));
        assert_eq!(chars.next_back(), None);
        assert_eq!(chars.next_back(), None);

        let strs = SplitStr::new(["Hello, ", "wÿrld!"]);
        let mut chars = strs.chars();
        assert_eq!(chars.next_back(), Some('!'));
        assert_eq!(chars.next_back(), Some('d'));
        assert_eq!(chars.next_back(), Some('l'));
        assert_eq!(chars.next_back(), Some('r'));
        assert_eq!(chars.next_back(), Some('ÿ'));
        assert_eq!(chars.next_back(), Some('w'));
        assert_eq!(chars.next_back(), Some(' '));
        assert_eq!(chars.next_back(), Some(','));
        assert_eq!(chars.next_back(), Some('o'));
        assert_eq!(chars.next_back(), Some('l'));
        assert_eq!(chars.next_back(), Some('l'));
        assert_eq!(chars.next_back(), Some('e'));
        assert_eq!(chars.next_back(), Some('H'));
        assert_eq!(chars.next_back(), None);
        assert_eq!(chars.next_back(), None);
    }

    #[test]
    fn test_char_indices() {
        let strs = SplitStr::new(["Hello, ", "world!"]);
        let mut chars = strs.char_indices();
        assert_eq!(chars.next(), Some((0, 'H')));
        assert_eq!(chars.next(), Some((1, 'e')));
        assert_eq!(chars.next(), Some((2, 'l')));
        assert_eq!(chars.next(), Some((3, 'l')));
        assert_eq!(chars.next(), Some((4, 'o')));
        assert_eq!(chars.next(), Some((5, ',')));
        assert_eq!(chars.next(), Some((6, ' ')));
        assert_eq!(chars.next(), Some((7, 'w')));
        assert_eq!(chars.next(), Some((8, 'o')));
        assert_eq!(chars.next(), Some((9, 'r')));
        assert_eq!(chars.next(), Some((10, 'l')));
        assert_eq!(chars.next(), Some((11, 'd')));
        assert_eq!(chars.next(), Some((12, '!')));
        assert_eq!(chars.next(), None);
        assert_eq!(chars.next(), None);

        let strs = SplitStr::new(["Hello, ", "wÿrld!"]);
        let mut chars = strs.char_indices();
        assert_eq!(chars.next(), Some((0, 'H')));
        assert_eq!(chars.next(), Some((1, 'e')));
        assert_eq!(chars.next(), Some((2, 'l')));
        assert_eq!(chars.next(), Some((3, 'l')));
        assert_eq!(chars.next(), Some((4, 'o')));
        assert_eq!(chars.next(), Some((5, ',')));
        assert_eq!(chars.next(), Some((6, ' ')));
        assert_eq!(chars.next(), Some((7, 'w')));
        assert_eq!(chars.next(), Some((8, 'ÿ')));
        assert_eq!(chars.next(), Some((10, 'r')));
        assert_eq!(chars.next(), Some((11, 'l')));
        assert_eq!(chars.next(), Some((12, 'd')));
        assert_eq!(chars.next(), Some((13, '!')));
        assert_eq!(chars.next(), None);
        assert_eq!(chars.next(), None);
    }

    #[test]
    fn test_char_indices_back() {
        let strs = SplitStr::new(["Hello, ", "world!"]);
        let mut chars = strs.char_indices();
        assert_eq!(chars.next_back(), Some((12, '!')));
        assert_eq!(chars.next_back(), Some((11, 'd')));
        assert_eq!(chars.next_back(), Some((10, 'l')));
        assert_eq!(chars.next_back(), Some((9, 'r')));
        assert_eq!(chars.next_back(), Some((8, 'o')));
        assert_eq!(chars.next_back(), Some((7, 'w')));
        assert_eq!(chars.next_back(), Some((6, ' ')));
        assert_eq!(chars.next_back(), Some((5, ',')));
        assert_eq!(chars.next_back(), Some((4, 'o')));
        assert_eq!(chars.next_back(), Some((3, 'l')));
        assert_eq!(chars.next_back(), Some((2, 'l')));
        assert_eq!(chars.next_back(), Some((1, 'e')));
        assert_eq!(chars.next_back(), Some((0, 'H')));
        assert_eq!(chars.next_back(), None);
        assert_eq!(chars.next_back(), None);

        let strs = SplitStr::new(["Hello, ", "wÿrld!"]);
        let mut chars = strs.char_indices();
        assert_eq!(chars.next_back(), Some((13, '!')));
        assert_eq!(chars.next_back(), Some((12, 'd')));
        assert_eq!(chars.next_back(), Some((11, 'l')));
        assert_eq!(chars.next_back(), Some((10, 'r')));
        assert_eq!(chars.next_back(), Some((8, 'ÿ')));
        assert_eq!(chars.next_back(), Some((7, 'w')));
        assert_eq!(chars.next_back(), Some((6, ' ')));
        assert_eq!(chars.next_back(), Some((5, ',')));
        assert_eq!(chars.next_back(), Some((4, 'o')));
        assert_eq!(chars.next_back(), Some((3, 'l')));
        assert_eq!(chars.next_back(), Some((2, 'l')));
        assert_eq!(chars.next_back(), Some((1, 'e')));
        assert_eq!(chars.next_back(), Some((0, 'H')));
        assert_eq!(chars.next_back(), None);
        assert_eq!(chars.next_back(), None);
    }
}
