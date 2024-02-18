use itertools::Itertools;
use num::{bigint::ToBigUint, BigUint, Integer};
use proptest::strategy::Strategy;

use super::group::*;
use rand::seq::SliceRandom;
use std::collections::HashSet;

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct SymmetricGroup {
    pub degree: usize,
}

#[derive(Clone, Debug, Hash)]
pub struct Cycle {
    pub degree: usize,
    pub vec: Vec<usize>,
}

impl From<Cycle> for Permutation {
    fn from(value: Cycle) -> Self {
        let i = value.vec.iter();
        let mut v: Vec<usize> = (0..value.degree).collect();
        for (&n, &m) in i.clone().zip(i.skip(1).cycle()) {
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
struct Permutation {
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
    fn new(degree: usize, vec: Vec<usize>) -> Result<Permutation, PermutationError> {
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

    fn strategy(degree: usize) -> impl Strategy<Value = Permutation> {
        return (0..1).prop_perturb(move |_, mut rng| {
            let mut vec: Vec<usize> = (0..degree).collect();
            vec.shuffle(&mut rng);
            Permutation { degree, vec }
        });
    }

    fn decompose_cycle(&self) -> Vec<Cycle> {
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
        cycles
    }
}

impl GroupLike<Permutation> for SymmetricGroup {
    fn op(&self, x: Permutation, y: Permutation) -> Permutation {
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

    fn inv(&self, x: Permutation) -> Permutation {
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
mod test {
    use crate::group::{Group, GroupLike};
    use num::bigint::ToBigUint;
    use proptest::prelude::*;

    use super::*;

    prop_compose! {
        fn group_perm(k: usize)(n in 0..k)
                        (grp in Just(SymmetricGroup {degree : n}), perm in Permutation::strategy(n))
                        -> (SymmetricGroup, Permutation) {
           (grp, perm)
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

          #[test]
        fn symmetric_group_element_order((grp, perm) in group_perm(100)) {
            match grp.order_of(&perm).into() {
                NNInf::Inf => panic!(),
                NNInf::Fin(a) =>
                { assert_eq!(grp.power_bigint(perm, (a.clone()).into()), grp.id()); }
            }

        }

        }
}
