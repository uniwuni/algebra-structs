use num::BigUint;

#[derive(Eq, Clone, PartialEq, PartialOrd, Ord)]
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
