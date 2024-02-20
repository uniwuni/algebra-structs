use std::collections::HashSet;

use num::BigUint;

#[derive(Eq, Clone, PartialEq, PartialOrd, Ord, Debug)]
/// Natural numbers plus a point at infinity. Useful for orders of group elements, characteristics, etc.
pub enum NNInf {
    Fin(BigUint),
    Inf,
}

/// Types of subgroups, subrings, etc.
pub trait Subobject<A, B> {
    /// Return the ambient structure `self` is a substructure of.
    fn ambient(&self) -> B;
}

pub fn vec_is_subset_iterator<A: Eq + std::hash::Hash + Clone, I: Iterator<Item = A>>(vec: &Vec<A>, iter: I) -> bool {
    let mut h: HashSet<A> = HashSet::new();
    let v: HashSet<A> = HashSet::from_iter(vec.iter().cloned());
    let mut empty = true;
    for x in iter {
        empty = false;
        if v.contains(&x) {
            h.insert(x);
        }
        if v.is_subset(&h) {
            return true;
        }
    }
    empty
}
