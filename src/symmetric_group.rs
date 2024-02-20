use itertools::Itertools;
use num::{bigint::ToBigUint, BigUint, Integer};
use num_traits::One;
use proptest::strategy::Strategy;

use crate::misc::NNInf;

use super::group::*;
use rand::seq::SliceRandom;
use std::collections::{HashMap, HashSet};

/// Symmetric groups of a given `degree`.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct SymmetricGroup {
    pub degree: usize,
}

#[derive(Clone, Debug, Hash, PartialEq, Eq)]
#[non_exhaustive]
/// Cyclic permutations of a given `degree`.
pub struct Cycle {
    pub degree: usize,
    pub vec: Vec<usize>,
}

impl From<&Cycle> for Permutation {
    /// Turn cycles into permutations in the canonical way.
    /// # Runtime
    /// O(ord(value)), about 2 ord(value) steps.
    fn from(value: &Cycle) -> Self {
        let i = value.vec.iter();
        let mut v: Vec<usize> = (0..value.degree).collect();
        for (&n, &m) in i.clone().zip(i.cycle().skip(1)) {
            v[n] = m;
        }
        Self {
            degree: value.degree,
            vec: v,
        }
    }
}

impl From<Cycle> for Permutation {
    /// Turn cycles into permutations in the canonical way.
    /// # Runtime
    /// O(ord(value)), about 2 ord(value) steps.
    fn from(value: Cycle) -> Self {
        (&value).into()
    }
}
impl Cycle {
    /// Returns a permutation of `degree` that cycles through the given `vec` in order.
    /// This normalizes the cycle so it starts with the lowest element, thus `Cycle::new(degree,vec).vec == vec`
    /// does not always hold.
    /// # Errors
    /// * If some element of the vector is too big for the symmetric group to act on, a [`PermutationError::NotBounded`] is returned.
    /// * If a value appears twice, a [`PermutationError::NotInjective`] is returned.
    /// # Runtime
    /// O(`degree`), worst-case three iterations through `vec`.
    pub fn new(degree: usize, vec: Vec<usize>) -> Result<Self, PermutationError> {
        let mut vec = vec;
        let mut set: HashSet<usize> = HashSet::new();
        let l = vec.len();
        for &x in &vec {
            if x >= degree {
                return Err(PermutationError::NotBounded);
            }
            set.insert(x);
        }
        if set.len() != l {
            return Err(PermutationError::NotInjective);
        }
        if let Some(n) = vec.iter().position_min() {
            vec.rotate_left(n); // normalize start position
        }
        Ok(Self { degree, vec })
    }
    fn new_no_check(degree: usize, vec: Vec<usize>) -> Self {
        let mut vec = vec;
        if let Some(n) = vec.iter().position_min() {
            vec.rotate_left(n); // normalize start position
        }
        Self { degree, vec }
    }
    /// Order of a cycle as a permutation.
    /// # Runtime
    /// O(1).
    pub fn order(&self) -> usize {
        self.vec.len()
    }
    /// Inverse of a cycle as a cycle.
    /// # Runtime
    /// O(`degree`) due to reversal, up to 3 iterations due to normalization.
    pub fn inv(self) -> Self {
        let mut s = self.vec;
        s.reverse();
        Self::new_no_check(self.degree, s)
    }

    /// Proptest [`Strategy`] to generate cycles of given `degree`.
    /// Not really uniform, but uniform in cycle length and per length uniform in value.
    pub fn strategy(degree: usize) -> impl Strategy<Value = Self> {
        (0..=degree).prop_perturb(move |n, mut rng| {
            let mut vec: Vec<usize> = (0..degree).collect();
            vec.shuffle(&mut rng);
            vec.truncate(n);
            Self::new_no_check(degree, vec)
        })
    }
    /// Proptest [`Strategy`] to generate cycles up to given `degree` as well as the corresponding degree.
    pub fn strategy_up_to(degree: usize) -> impl Strategy<Value = (usize, Self)> {
        (0..degree).prop_flat_map(|n| (proptest::strategy::Just(n), Self::strategy(n)))
    }
}

#[derive(Clone, PartialEq, Eq, Debug, Hash)]
pub enum PermutationError {
    WrongSize,
    NotInjective,
    NotBounded,
}

#[derive(Clone, PartialEq, Eq, Debug, Hash)]
pub struct Permutation {
    pub degree: usize,
    pub vec: Vec<usize>,
}

impl std::ops::Index<usize> for Permutation {
    type Output = usize;

    fn index(&self, index: usize) -> &Self::Output {
        &self.vec[index]
    }
}

/// Represents a permutation in some (finite) symmetric group.
/// The degree of the group is part of the permutation data to avoid complicated type level machinery.
impl Permutation {
    /// Returns a new permutation given the `degree` and a `vec` of how it acts on `0..degree`.
    /// # Errors
    /// * [`PermutationError::WrongSize`] if `vec.len() != degree`.
    /// * [`PermutationError::NotBounded`] if some value in `vec` is greater or equal to `degree`.
    /// * [`PermutationError::NotInjective`] if some value in `vec` appears twice.
    pub fn new(degree: usize, vec: Vec<usize>) -> Result<Self, PermutationError> {
        let mut set: HashSet<usize> = HashSet::new();
        if vec.len() != degree {
            return Err(PermutationError::WrongSize);
        }
        for &x in &vec {
            if x >= degree {
                return Err(PermutationError::NotBounded);
            }
            set.insert(x);
        }
        if set.len() != degree {
            return Err(PermutationError::NotInjective);
        }
        Ok(Self { degree, vec })
    }
    /// Proptest [`Strategy`] to generate permutations of given `degree`.
    /// More or less uniform.
    pub fn strategy(degree: usize) -> impl Strategy<Value = Self> {
        (0..1).prop_perturb(move |_, mut rng| {
            let mut vec: Vec<usize> = (0..degree).collect();
            vec.shuffle(&mut rng);
            Self { degree, vec }
        })
    }
    /// Proptest [`Strategy`] to generate permutations of degree less than `degree`.
    /// Uniform in the degree.
    pub fn strategy_up_to(degree: usize) -> impl Strategy<Value = (usize, Self)> {
        (0..degree).prop_flat_map(|n| (proptest::strategy::Just(n), Self::strategy(n)))
    }
    /// Proptest [`Strategy`] to generate two permutations of degree less than `degree`.
    /// Uniform in the degree.
    pub fn strategy_up_to2(degree: usize) -> impl Strategy<Value = (usize, Self, Self)> {
        (0..degree).prop_flat_map(|n| (proptest::strategy::Just(n), Self::strategy(n), Self::strategy(n)))
    }
    /// Decompose the permutation into [`Cycle`]s. These are ordered by length.
    /// # Runtime
    /// Approximately O(n log n) due to HashSet usage.
    pub fn decompose_cycle(&self) -> Vec<Cycle> {
        let mut unvisited: HashSet<usize> = (0..self.degree).collect();
        let mut cycles: Vec<Cycle> = vec![];
        while let Some(&start) = unvisited.iter().min() {
            let mut m: usize = start; // kind of hacky but who care
            let mut v: Vec<usize> = vec![start];
            let mut b: bool = true;
            while m != start || b {
                b = false;
                m = self[m];
                v.push(m);
                unvisited.remove(&m);
            }
            v.pop();
            cycles.push(Cycle {
                degree: self.degree,
                vec: v,
            });
        }
        cycles.sort_by(|x, y| x.degree.cmp(&y.degree));
        cycles
    }
}

#[derive(PartialEq, Eq, Debug, Clone)]
pub struct ConjugacyType {
    degree: usize,
    amounts: HashMap<usize, usize>,
}

pub enum ConjugacyTypeError {
    SumWrong,
}

impl ConjugacyType {
    /// Given a `degree` and a hashmap of how often each cycle length occurs, return the conjugacy type defined
    /// by these cycle lengths. Note that fixpoints have cycle length 1.
    /// # Errors
    /// Yields a [`ConjugacyTypeError::SumWrong`] if the sum of all cycle lengths
    /// (that is all key-value products) does not equal the degree.
    pub fn new(degree: usize, amounts: HashMap<usize, usize>) -> Result<Self, ConjugacyTypeError> {
        let mut amounts = amounts;
        amounts.remove(&0);
        let mut inferred_degree = 0;
        for (cycle_length, amount) in &amounts {
            inferred_degree += cycle_length * amount;
        }
        if inferred_degree == degree {
            Ok(Self { degree, amounts })
        } else {
            Err(ConjugacyTypeError::SumWrong)
        }
    }

    fn uncount(&self) -> Vec<usize> {
        let mut v: Vec<usize> = vec![];
        self.amounts.iter().for_each(|(ln, am)| {
            v.extend(vec![ln; *am]);
        });
        v
    }
}

impl ConjugacyType {
    fn make_from_remaining(
        degree: usize,
        cycles: Vec<usize>,
        remaining: HashSet<usize>,
    ) -> impl Iterator<Item = Vec<Cycle>>  {
        let mut cycles = cycles;
        if remaining.is_empty() {
            itertools::Either::Left(std::iter::once(SymmetricGroup { degree }.id().decompose_cycle()))
        } else {
            let len = cycles.pop().unwrap();
            if len == 0 {
                return itertools::Either::Left(std::iter::once(vec![]));
            }
            let options: itertools::Unique<_> = remaining.clone()
                .into_iter()
                .permutations(len)
                .map(move |x| Cycle::new_no_check(degree, x.iter().copied().collect()))
                .unique();
            itertools::Either::Right(options
                .flat_map(move |x| {
                    let new_remaining =
                        &remaining.clone() - &x.vec.iter().copied().collect::<HashSet<usize>>();
                    let mut res: Vec<_> = Self::make_from_remaining(degree, cycles.clone(), new_remaining).collect();
                    for m in &mut res {
                        m.push(x.clone());
                    }
                    res
                }))
        }
    }
    /// Compute cardinality of conjugacy type.
    /// # Runtime
    /// Approximately O(n)
    pub fn len(&self) -> BigUint {
        let cs = self.uncount();
        let mut n = BigUint::one();
        let mut remaining = self.degree;
        for c in cs {
            let m: usize = ((remaining - c + 1)..=remaining).product::<usize>() / c;
            if m != 0 {
                n *= BigUint::from(m);
            }
            remaining -= c;
        }
        n
    }
}


impl IntoIterator for ConjugacyType {
    type Item = Permutation;

    type IntoIter = Box<dyn Iterator<Item = Permutation>>;
    // TODO write a proper iterator
    /// Yield all elements of a certain conjugacy type.
    fn into_iter(self) -> Self::IntoIter {
        let range: HashSet<usize> = (0..self.degree).collect();
        Box::new(Self::make_from_remaining(self.degree, self.uncount(),range)
            .map(move |a| {
                let s = SymmetricGroup {
                    degree: self.degree,
                };
                a.iter().fold(s.id(), |x, y| s.op(&x, &y.into()))
            }))
    }
}

impl Permutation {
    /// Compute conjugacy type by using the cycle decomposition
    fn conjugacy_type(&self) -> ConjugacyType {
        let orders = self
            .decompose_cycle()
            .into_iter()
            .map(|x| x.order())
            .counts();
        ConjugacyType {
            degree: self.degree,
            amounts: orders,
        }
    }
}

impl GroupLike<Permutation> for SymmetricGroup {
    /// Computes the composition of two permutations such that `self.op(x,y)[n] = x[y[n]]`.
    /// # Panics
    /// If the degree of either of the permutations does not match the degree of the group.
    fn op(&self, x: &Permutation, y: &Permutation) -> Permutation {
        assert_eq!(self.degree, x.degree);
        assert_eq!(self.degree, y.degree);
        Permutation {
            degree: self.degree,
            vec: (0..self.degree).map(|n| x[y[n]]).collect(),
        }
    }
    /// Returns the identity permutation 0,1,..,`self.degree - 1` of the symmetric group.
    fn id(&self) -> Permutation {
        Permutation {
            degree: self.degree,
            vec: (0..self.degree).collect(),
        }
    }
    /// Computes the inverse of a permutation such that `self.inv(x)[n] = m` if and only if `self.x[m] = n`.
    /// # Panics
    /// If the degree of the permutation does not match the degree of the group.
    fn inv(&self, x: &Permutation) -> Permutation {
        assert_eq!(self.degree, x.degree);
        let mut v: Vec<usize> = vec![0; self.degree];
        for (n, i) in x.vec.iter().enumerate() {
            v[*i] = n;
        }
        Permutation {
            degree: self.degree,
            vec: v,
        }
    }
}

impl FiniteGroupLike<Permutation> for SymmetricGroup {
    fn all_elements(&self) -> impl Iterator<Item = Permutation> {
        (0..(self.degree))
            .permutations(self.degree)
            .map(|x| Permutation {
                degree: self.degree,
                vec: x,
            })
    }
    fn order(&self) -> num::BigUint {
        let mut n: BigUint = num_traits::One::one();
        for i in 1..=self.degree {
            n *= BigUint::from(i);
        }
        n
    }
}

impl OrderGroupLike<Permutation> for SymmetricGroup {
    /// Computes order via cycle decomposition.
    /// # Runtime
    /// Approximately O(n log n).
    fn order_of(&self, x: &Permutation) -> NNInf {
        assert_eq!(self.degree, x.degree);
        let orders = x
            .decompose_cycle()
            .into_iter()
            .map(|a| a.order().to_biguint().unwrap());
        NNInf::Fin(orders.fold(num_traits::Zero::zero(), |x, y: BigUint| y.lcm(&x)))
    }
}

impl ConjugacyGroupLike<Permutation> for SymmetricGroup {
    /// Check conjugacy of permutations via cycle decomposition and the symmetric group acting on itself.
    /// # Runtime
    /// Approximately O(n log n).
    fn are_conjugate(&self, x: &Permutation, y: &Permutation) -> Option<Permutation> {
        assert_eq!(self.degree, x.degree);
        assert_eq!(self.degree, y.degree);
        if x.conjugacy_type() != y.conjugacy_type() {
            return None;
        }
        let dx = Permutation {
            degree: self.degree,
            vec: x
                .decompose_cycle()
                .iter()
                .flat_map(|x| &x.vec)
                .copied()
                .collect(),
        };
        let dy = Permutation {
            degree: self.degree,
            vec: y
                .decompose_cycle()
                .iter()
                .flat_map(|x| &x.vec)
                .copied()
                .collect(),
        };
        Some(self.op(&dy, &self.inv(&dx)))
    }
}

mod test {
    #[allow(unused_imports)]
    use num_traits::Zero;
    use proptest::prelude::*;

    use super::*;
    #[test]
    fn cycle_test() {
        let c = Cycle::new(5, vec![0, 1, 2]).map(Permutation::from);
        assert_eq!(c, Permutation::new(5, vec![1, 2, 0, 3, 4]));
    }

    #[test]
    fn conjugacy_test() {
        let c = Permutation::new(5, vec![1, 2, 0, 4, 3]).unwrap();
        let d = Permutation::new(5, vec![1, 4, 3, 2, 0]).unwrap();
        let g = SymmetricGroup { degree: 5 };
        if let Some(x) = g.are_conjugate(&c, &d) {
            dbg!(&x);
            dbg!(g.op(&x, &g.op(&c, &g.inv(&x))), d);
        }
    }
    #[test]
    fn conjugacy_class_test() {
        let c = Permutation::new(9, vec![1, 2, 4, 8, 7, 3, 6, 5, 0])
            .unwrap()
            .conjugacy_type()
            .into_iter()
            .count();
        dbg!(c);
    }
    prop_compose! {
        fn group_perm(k: usize)(n in 0..k)
                        (grp in Just(SymmetricGroup {degree : n}), perm in Permutation::strategy(n))
                        -> (SymmetricGroup, Permutation) {
           (grp, perm)
       }
    }
    prop_compose! {
       fn group_perm2(k: usize)(n in 0..k)
                        (grp in Just(SymmetricGroup {degree : n}), perm in Permutation::strategy(n), perm2 in Permutation::strategy(n))
                        -> (SymmetricGroup, Permutation, Permutation) {
           (grp, perm, perm2)
       }
    }
    proptest! {

         #![proptest_config(ProptestConfig::with_cases(20))]
         #[test]
         fn symmetric_group_is_group(n in 0..500usize) {
             let g = SymmetricGroup {degree : n};
             Group::<Permutation>::new(
                 Box::new(move |x,y| g.op(x,y)),
                 g.id(),
                 Box::new(move |x| g.inv(x)), &Permutation::strategy(n).boxed()).unwrap();
         }
         #[test]
         fn symmetric_group_order(n in 0..9usize) {
             let g = SymmetricGroup {degree : n};
             assert_eq!(g.all_elements().count().to_biguint(), Some(g.order()))
         }
    }
    proptest! {
         #[test]
         fn symmetric_group_element_order((n, perm) in Permutation::strategy_up_to(100)){
             let grp = SymmetricGroup { degree: n };
             match grp.order_of(&perm) {
                 NNInf::Inf => panic!(),
                 NNInf::Fin(a) =>
                 {
                     assert_eq!(grp.power_bigint(&perm, (a.clone()).into()), grp.id());
                     if !a.clone().is_zero() {
                       assert_ne!(grp.power_bigint(&perm, (a.clone() / (2u8)).into()), grp.id());
                     }
                 }
             }
         }
         #[test]
         fn symmetric_group_cycle_decomposition((n, perm) in Permutation::strategy_up_to(10000)) {
             let grp = SymmetricGroup { degree: n };
             let cycles = perm.decompose_cycle();
             let cycle_perms = cycles.iter().map(Permutation::from);
             assert_eq!(perm, cycle_perms.fold(grp.id(), |x, y| grp.op(&x,&y)));
         }
        #[test]
         fn symmetric_group_conjugacy_type_conjugate((k, perm) in Permutation::strategy_up_to(9), n in 0..10000000usize) {
             let grp = SymmetricGroup { degree: k };
             let conjs: Vec<Permutation> = perm.conjugacy_type().into_iter().collect();
             let conj = &conjs[n % conjs.len()];
             assert!(grp.are_conjugate(conj, &perm).is_some())
         }
        #[test]
         fn symmetric_group_conjugate_in_conjugacy_type((k, perm, perm2) in Permutation::strategy_up_to2(9)) {
             let grp = SymmetricGroup { degree: k };
             let mut conjs = perm.conjugacy_type().into_iter();
             let conjugate = grp.op(&grp.inv(&perm2), &grp.op(&perm, &perm2));

             assert!(conjs.contains(&conjugate));
         }
        #[test]
         fn symmetric_group_conjugacy_type_size((_, perm) in Permutation::strategy_up_to(9)) {
             let conj = perm.conjugacy_type();
             assert_eq!(conj.len(),conj.into_iter().count().into());
         }

        #[test]
        fn cycle_inv_to_perm_commute((n, cycle) in Cycle::strategy_up_to(256)) {
            let grp = SymmetricGroup { degree: n };
            assert_eq!(Permutation::from(cycle.clone().inv()), grp.inv(&Permutation::from(cycle)));

        }
        #[test]
        fn cycle_decomposes_to_nearly_itself((n, cycle) in Cycle::strategy_up_to(256)) {
            if cycle.order() > 1 {assert_eq!(Permutation::from(&cycle).decompose_cycle().iter().filter(|a| a.order() != 1).collect::<Vec<_>>(),
                                 vec![&cycle])};

        }
    }
    proptest! {

        #![proptest_config(ProptestConfig::with_cases(5))]
        #[test]
        #[cfg_attr(not(feature = "intensive_test"), ignore)]
        fn symmetric_group_conjugacy_type_hard(perm in Permutation::strategy(10)) {
             let conj = perm.conjugacy_type();
             dbg!(conj.len());
             assert_eq!(conj.len(),conj.into_iter().count().into());
        }
    }
}


/// Subgroups of symmetric groups.
/// To make pretty much any algorithm viable, this needs to store all its elements.
/// In the cases where this would be an issue, computing anything about the group would be problematic either way.
pub struct PermutationSubgroup {
    ambient: SymmetricGroup,
    gens: Vec<Permutation>,
    elems: HashSet<Permutation>
}

impl GroupLike<Permutation> for PermutationSubgroup {
    fn op(&self, x: &Permutation, y: &Permutation) -> Permutation {
        assert!(self.elems.contains(x));
        assert!(self.elems.contains(y));
        self.ambient.op(x,y)
    }

    fn id(&self) -> Permutation {
        self.ambient.id()
    }

    fn inv(&self, x: &Permutation) -> Permutation {
        assert!(self.elems.contains(x));
        self.ambient.inv(x)
    }
}
