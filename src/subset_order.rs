#![warn(missing_docs)]

use ::*;

use std::hash::{Hash};
use std::cmp::{Ordering};
#[cfg(test)]
use std::iter::{FromIterator};

/// Test the degree to which the RHS is contained by the LHS.
/// * A result of `Equal` means that the LHS exactly
/// matches on all RHS elements.
/// * A result of `Greater` means that the LHS contains
/// all present RHS elements and overcontains at least one.
/// * A result of `Less` means only that the containment
/// does not hold.
fn containment<T>(lhs: &HashMultiSet<T>,
                  rhs: &HashMultiSet<T>) -> Ordering
    where T: Eq + Hash + Clone
{
    let mut result = Ordering::Equal;
    for val in rhs.distinct_elements() {
        let nlhs = lhs.count_of(val.clone());
        if nlhs == 0 {
            return Ordering::Less;
        };
        let nrhs = rhs.count_of(val.clone());
        if nrhs > nlhs {
            return Ordering::Less;
        } else if nrhs < nlhs {
            result = Ordering::Greater;
        };
    };
    result
}

#[test]
fn test_containment() {
    let s1: HashMultiSet<isize> = FromIterator::from_iter(vec![1,2,3]);
    let s2: HashMultiSet<isize> = FromIterator::from_iter(vec![1,1,4]);
    let s3: HashMultiSet<isize> = FromIterator::from_iter(vec![2,3]);
    let s4: HashMultiSet<isize> = FromIterator::from_iter(vec![1,4]);
    assert_eq!(Ordering::Equal, containment(&s1, &s1));
    assert_eq!(Ordering::Less, containment(&s1, &s2));
    assert_eq!(Ordering::Less, containment(&s2, &s1));
    assert_eq!(Ordering::Equal, containment(&s1, &s3));
    assert_eq!(Ordering::Less, containment(&s3, &s1));
    assert_eq!(Ordering::Greater, containment(&s2, &s4));
}

impl<T> PartialOrd for HashMultiSet<T> where
    T: Eq + Hash + Clone
{
    /// MultiSets are partial-ordered by containment: if they
    /// are equal, they are `Equal`; if one is a proper subset
    /// of the other they are `Less` or `Greater`; otherwise
    /// they are unordered.
    ///
    /// # Examples
    ///
    /// ```
    /// use multiset::HashMultiSet;
    /// use std::iter::FromIterator;
    /// use std::cmp::Ordering;
    ///
    /// let s1: HashMultiSet<isize> = FromIterator::from_iter(vec![1,2,3]);
    /// let s2: HashMultiSet<isize> = FromIterator::from_iter(vec![1,1,4]);
    /// let s3: HashMultiSet<isize> = FromIterator::from_iter(vec![2,3]);
    /// let s4: HashMultiSet<isize> = FromIterator::from_iter(vec![1,1,2,3]);
    /// assert_eq!(None, s1.partial_cmp(&s2));
    /// assert_eq!(Some(Ordering::Less), s3.partial_cmp(&s1));    
    /// assert_eq!(Some(Ordering::Less), s1.partial_cmp(&s4));
    /// assert_eq!(Some(Ordering::Greater), s1.partial_cmp(&s3));
    /// assert_eq!(Some(Ordering::Equal), s1.partial_cmp(&s1));
    /// assert_eq!(Some(Ordering::Greater), s4.partial_cmp(&s1));
    /// ```
    fn partial_cmp(&self, other: &HashMultiSet<T>) -> Option<Ordering> {
        match containment(self, other) {
            Ordering::Less => {
                match containment(other, self) {
                    Ordering::Less => None,
                    _ => Some(Ordering::Less)
                }
            },
            Ordering::Equal => {
                match containment(other, self) {
                    Ordering::Less => Some(Ordering::Greater),
                    Ordering::Equal => Some(Ordering::Equal),
                    Ordering::Greater => panic!("=> ordering observed")
                }
            },
            Ordering::Greater => Some(Ordering::Greater)
        }
    }

    /// The RHS contains the LHS. This is computed more efficiently
    /// than with `partial_cmp()` in some cases.
    ///
    /// # Examples
    ///
    /// ```
    /// use multiset::HashMultiSet;
    /// use std::iter::FromIterator;
    ///
    /// let s1: HashMultiSet<isize> = FromIterator::from_iter(vec![1,2,3]);
    /// let s2: HashMultiSet<isize> = FromIterator::from_iter(vec![1,1,4]);
    /// let s3: HashMultiSet<isize> = FromIterator::from_iter(vec![2,3]);
    /// assert!(s1 <= s1);
    /// assert!(s3 <= s1);
    /// assert!(!(s1 <= s2));
    /// assert!(!(s2 <= s1));
    /// assert!(!(s1 <= s3));
    /// ```
    fn le(&self, other: &HashMultiSet<T>) -> bool {
        containment(other, self) != Ordering::Less
    }

    /// The LHS contains the RHS. This is computed more efficiently
    /// than with `partial_cmp()` in some cases.
    ///
    /// # Examples
    ///
    /// ```
    /// use multiset::HashMultiSet;
    /// use std::iter::FromIterator;
    ///
    /// let s1: HashMultiSet<isize> = FromIterator::from_iter(vec![1,2,3]);
    /// let s2: HashMultiSet<isize> = FromIterator::from_iter(vec![1,1,4]);
    /// let s3: HashMultiSet<isize> = FromIterator::from_iter(vec![2,3]);
    /// assert!(s1 >= s1);
    /// assert!(s1 >= s3);
    /// assert!(!(s2 >= s1));
    /// assert!(!(s1 >= s2));
    /// assert!(!(s3 >= s1));
    /// ```
    fn ge(&self, other: &HashMultiSet<T>) -> bool {
        containment(self, other) != Ordering::Less
    }

}
