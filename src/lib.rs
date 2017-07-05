//! A multiset is an unordered collection of values. They are also
//! known as bags.
//!
//! Unlike sets where each value is either included or not, multisets
//! permit duplicates. Consequently, they're useful for maintaining a
//! count of distinct values.

mod multiset;
mod subset_order;

pub use multiset::{HashMultiSet};
