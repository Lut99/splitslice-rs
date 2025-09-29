//  LIB.rs
//    by Lut99
//
//  Description:
//!   TODO
//

// Declare the modules
pub mod slice;
pub mod str;

// Use the mains
pub use slice::SplitSlice;
pub use str::SplitStr;

/// Defines all of the traits and iterators that are useful to have in scope when working with this
/// crate.
pub mod prelude {
    pub use crate::slice::Iter;
    pub use crate::str::{CharIndices, Chars};
}
