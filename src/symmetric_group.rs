use itertools::Itertools;
use num::{bigint::ToBigUint, BigUint, Integer, integer::binomial};
use proptest::strategy::Strategy;

use super::group::*;
use rand::seq::SliceRandom;
use std::{
    collections::{HashMap, HashSet},
    iter::Map,
};

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct SymmetricGroup {
    pub degree: usize,
}

#[derive(Clone, Debug, Hash, PartialEq, Eq)]
pub struct Cycle {
    pub degree: usize,
    pub vec: Vec<usize>,
}

impl From<&Cycle> for Permutation {
    fn from(value: &Cycle) -> Self {
        let i = value.vec.iter();
        let mut v: Vec<usize> = (0..value.degree).collect();
        for (&n, &m) in i.clone().zip(i.cycle().skip(1)) {
            v[n] = m;
        }
        Permutation {
            degree: value.degree,
            vec: v,
        }
    }
}

impl Cycle {
    fn new(degree: usize, vec: Vec<usize>) -> Result<Cycle, PermutationError> {
        let mut vec = vec;
        let mut set: HashSet<usize> = HashSet::new();
        let l = vec.len();
        if l > degree {
            return Err(PermutationError::WrongSize);
        }
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
        return Ok(Cycle { degree, vec });
    }

    fn order(self) -> usize {
        self.vec.len()
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

impl Permutation {
    pub fn new(degree: usize, vec: Vec<usize>) -> Result<Permutation, PermutationError> {
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
        return Ok(Permutation { degree, vec });
    }

    pub fn strategy(degree: usize) -> impl Strategy<Value = Permutation> {
        return (0..1).prop_perturb(move |_, mut rng| {
            let mut vec: Vec<usize> = (0..degree).collect();
            vec.shuffle(&mut rng);
            Permutation { degree, vec }
        });
    }

    pub fn decompose_cycle(&self) -> Vec<Cycle> {
        let mut unvisited: HashSet<usize> = HashSet::from_iter(0..self.degree);
        let mut cycles: Vec<Cycle> = vec![];
        while let Some(&start) = unvisited.iter().min() {
            let mut m: usize = start; // kind of hacky but who care
            let mut v: Vec<usize> = vec![];
            let mut b: bool = true;
            while m != start || b {
                b = false;
                m = self[m];
                v.push(m);
                unvisited.remove(&m);
            }
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
    pub fn new(
        degree: usize,
        amounts: HashMap<usize, usize>,
    ) -> Result<ConjugacyType, ConjugacyTypeError> {
        let mut amounts = amounts;
        amounts.remove(&0);
        let mut inferred_degree = 0;
        for (cycle_length, amount) in &amounts {
            inferred_degree += cycle_length * amount;
        }
        if inferred_degree != degree {
            Err(ConjugacyTypeError::SumWrong)
        } else {
            Ok(ConjugacyType { degree, amounts })
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
    ) -> Vec<Vec<Cycle>> {
        let mut cycles = cycles;
        if remaining.is_empty() {
            return vec![SymmetricGroup { degree }.id().decompose_cycle()];
        } else {
            let len = cycles.pop().unwrap();
            if len == 0 {
                return vec![vec![]];
            }
            let options = remaining.iter().permutations(len)
                                          .map(|x| Cycle::new(degree, x.iter().copied().copied().collect()).unwrap()).unique();
            options
                .map(|x| {
                    let new_remaining =
                        &remaining.clone() - &x.vec.iter().copied().collect::<HashSet<usize>>();
                    let mut res = Self::make_from_remaining(degree, cycles.clone(), new_remaining);
                    res.iter_mut().for_each(|m| {
                        m.push(x.clone());
                    });
                    res
                })
                .flatten()
                .collect()
        }
    }
    pub fn len(&self) -> BigUint {
        let cs = self.uncount();
        let mut n = 1.to_biguint().unwrap();
        let mut remaining = self.degree;
        for c in cs {
            let m: usize = (remaining-c+1..remaining+1).product::<usize>()/c;
            if m != 0 {
                n *= m.to_biguint().unwrap();
            }
            remaining -= c;
        }
        n
    }
}

impl IntoIterator for ConjugacyType {
    type Item = Permutation;

    type IntoIter = std::vec::IntoIter<Permutation>;

    fn into_iter(self) -> Self::IntoIter {
        let v = Self::make_from_remaining(self.degree, self.uncount(), (0..self.degree).collect());
        Self::make_from_remaining(self.degree, self.uncount(), (0..self.degree).collect())
            .iter()
            .map(move |a| {
                let s = SymmetricGroup {
                    degree: self.degree,
                };
                a.iter().fold(s.id(), |x, y| s.op(&x, &y.into()))
            })
            .collect::<Vec<_>>()
            .into_iter()
    }
}

impl Permutation {
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
    fn op(&self, x: &Permutation, y: &Permutation) -> Permutation {
        assert_eq!(self.degree, x.degree);
        assert_eq!(self.degree, y.degree);
        return Permutation {
            degree: self.degree,
            vec: (0..self.degree).map(|n| x[y[n]]).collect(),
        };
    }

    fn id(&self) -> Permutation {
        return Permutation {
            degree: self.degree,
            vec: (0..self.degree).collect(),
        };
    }

    fn inv(&self, x: &Permutation) -> Permutation {
        assert_eq!(self.degree, x.degree);
        let mut v: Vec<usize> = vec![0; self.degree];
        for (n, i) in x.vec.iter().enumerate() {
            v[*i] = n;
        }
        return Permutation {
            degree: self.degree,
            vec: v,
        };
    }
}

impl FiniteGroupLike<Permutation> for SymmetricGroup {
    fn all_elements(&self) -> HashSet<Permutation> {
        HashSet::from_iter(
            (0..(self.degree))
                .permutations(self.degree)
                .map(|x| Permutation {
                    degree: self.degree,
                    vec: x,
                }),
        )
    }
    fn order(&self) -> num::BigUint {
        let mut n: BigUint = num_traits::One::one();
        for i in 1..(self.degree + 1) {
            n *= i.to_biguint().unwrap();
        }
        n
    }
}

impl OrderGroupLike<Permutation> for SymmetricGroup {
    fn order_of(&self, x: &Permutation) -> NNInf {
        assert_eq!(self.degree, x.degree);
        let orders = x
            .decompose_cycle()
            .into_iter()
            .map(|a| a.order().to_biguint().unwrap());
        NNInf::Fin(orders.fold(num_traits::Zero::zero(), |x, y| y.lcm(&x)))
    }
}

impl ConjugacyGroupLike<Permutation> for SymmetricGroup {
    fn are_conjugate(&self, x: &Permutation, y: &Permutation) -> Option<Permutation> {
        assert_eq!(self.degree, x.degree);
        assert_eq!(self.degree, y.degree);
        if x.conjugacy_type() != y.conjugacy_type() {
            None
        } else {
            let dx = Permutation {
                degree: self.degree,
                vec: x
                    .decompose_cycle()
                    .iter()
                    .map(|x| &x.vec)
                    .flatten()
                    .copied()
                    .collect(),
            };
            let dy = Permutation {
                degree: self.degree,
                vec: y
                    .decompose_cycle()
                    .iter()
                    .map(|x| &x.vec)
                    .flatten()
                    .copied()
                    .collect(),
            };
            Some(self.op(&dy, &self.inv(&dx)))
        }
    }
}

mod test {
    use crate::group::{Group, GroupLike};
    use num::bigint::ToBigUint;
    use num_traits::Zero;
    use proptest::prelude::*;
    use rand::seq::index::IndexVecIter;

    use super::*;
    #[test]
    fn cycle_test() {
        let c = Cycle::new(5, vec![0, 1, 2]).unwrap();
        assert_eq!(
            Ok(Permutation::from(&c)),
            Permutation::new(5, vec![1, 2, 0, 3, 4])
        );
    }

    #[test]
    fn conjugacy_test() {
        //        let c = Permutation::from(&Cycle::new(5, vec![0, 2]).unwrap());
        //        let d = Permutation::from(&Cycle::new(5, vec![2, 3]).unwrap());
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
        let c = Permutation::new(9, vec![1, 2, 4, 8, 7, 3,6,5,0])
            .unwrap()
            .conjugacy_type().into_iter().len();
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
                 Box::new(move |x| g.inv(x)), Permutation::strategy(n).boxed()).unwrap();
         }
         #[test]
         fn symmetric_group_order(n in 0..10usize) {
             let g = SymmetricGroup {degree : n};
             assert_eq!(g.all_elements().len().to_biguint(), Some(g.order()))
         }
    }
    proptest! {
         #[test]
         fn symmetric_group_element_order((grp, perm) in group_perm(100)) {
             match grp.order_of(&perm).into() {
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
         fn symmetric_group_cycle_decomposition((grp, perm) in group_perm(100)) {
             let cycles = perm.decompose_cycle();
             let cycle_perms = cycles.iter().map(|x| Permutation::from(x));
             assert_eq!(perm, cycle_perms.fold(grp.id(), |x, y| grp.op(&x,&y)));
         }
        #[test]
         fn symmetric_group_conjugacy_type_conjugate((grp, perm) in group_perm(8), n in 0..10000000usize) {
             let conjs: Vec<Permutation> = perm.conjugacy_type().into_iter().collect();
             let conj = &conjs[n % &conjs.len()];
             assert!(grp.are_conjugate(&conj, &perm).is_some())
         }
        #[test]
         fn symmetric_group_conjugate_in_conjugacy_type((grp, perm, perm2) in group_perm2(8)) {

             let mut conjs = perm.conjugacy_type().into_iter();
             let conjugate = grp.op(&grp.inv(&perm2), &grp.op(&perm, &perm2));

             assert!(conjs.contains(&conjugate));
         }
        #[test]
         fn symmetric_group_conjugacy_type_size((_, perm) in group_perm(8)) {
             let conj = perm.conjugacy_type();
             assert_eq!(conj.len(),conj.into_iter().len().into());
         }
    }
}
