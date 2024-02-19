use num::BigInt;
use num::BigUint;
use num_traits::One;
use num_traits::Zero;
use proptest::prelude::*;
use proptest::test_runner::{Reason, TestError, TestRunner};
use std::collections::HashSet;
use std::collections::VecDeque;

use crate::misc::NNInf;

/// A type whose elements behave like groups.
pub trait GroupLike<A> {
    /// `g.op(x,y)` should yield the product of `x` and `y` with respect to the group `g`.
    fn op(&self, x: &A, y: &A) -> A;
    /// `g.id()` should yield the identity element of `g`.
    fn id(&self) -> A;
    /// `g.inv(x)` should yield the inverse of `x` with respect to the group `g`.
    fn inv(&self, x: &A) -> A;
    /// `g.power(x,n)` computes `x^n` with respect to the group `g`.
    /// # Runtime
    /// O(log(n)) calls of [`Self::op`].
    fn power(&self, x: &A, n: i64) -> A
    where
        A: Clone,
    {
        if n == 0 {
            self.id()
        } else if n < 0 {
            self.power(&self.inv(x), -n)
        } else if n == 1 {
            x.clone()
        } else if n % 2 == 0 {
            self.power(&self.op(x, x), n / 2)
        } else {
            self.op(x, &self.power(&self.op(x, x), n / 2))
        }
    }
    /// Same as [`Self::power`] but for [`BigInt`]s.
    fn power_bigint(&self, x: &A, n: BigInt) -> A
    where
        A: Clone,
    {
        if n == Zero::zero() {
            self.id()
        } else if n < Zero::zero() {
            self.power_bigint(&self.inv(x), (-1) * n)
        } else if n == One::one() {
            x.clone()
        } else if n.clone() % 2 == Zero::zero() {
            self.power_bigint(&self.op(x, x), n / 2_i8)
        } else {
            self.op(x, &self.power_bigint(&self.op(x, x), n / 2_i8))
        }
    }
}

/// Type whose elements are groups that also allow you to compute the order of an element.
/// Note that this does apply to all finite groups, but there is no blanket implementation
/// due to the performance cost and since usually, faster methods exist.
pub trait OrderGroupLike<A>: GroupLike<A> {
    /// Compute order of `x` with respect to the given group.
    fn order_of(&self, x: &A) -> NNInf;
}

/// Type of groups where one can decide conjugacy of elements.
pub trait ConjugacyGroupLike<A>: GroupLike<A> {
    /// Search for an a with axa^(-1) = y with respect to the given group.
    fn are_conjugate(&self, x: &A, y: &A) -> Option<A>;
}

/// Type whose elements are finite groups.
pub trait FiniteGroupLike<A>: GroupLike<A> {
    /// Compute order of group. Defaults to counting [`self.all_elements`].
    fn order(&self) -> BigUint where A: Eq + std::hash::Hash {
        self.all_elements().count().into()
    }
    /// Should return all elements of the group `self` and eventually end. This is not necessarily the same as
    /// all elements of `A`! For example, symmetric groups have wrappers around arbitrary-length `Vec`s as base types,
    /// despite permutations having fixed length. Each element should only occur once!
    fn all_elements(&self) -> impl Iterator<Item = A>;
    /// Bruteforces the order of `x`, which is possible due to finiteness.
    /// # Runtime
    /// Runs in O(ord(x)).
    fn bruteforce_order_of(&self, x: A) -> NNInf
    where
        A: Clone + PartialEq,
    {
        let mut y = x.clone();
        let mut n: u64 = 0;
        while y != self.id() {
            y = self.op(&y, &x);
            n += 1;
        }
        NNInf::Fin(BigUint::from(n))
    }
}

/// Arbitrary groups of which only their implementation of [`GroupLike`] is known.
pub struct Group<A> {
    op_fun: Box<dyn Fn(&A, &A) -> A>,
    id_val: A,
    inv_fun: Box<dyn Fn(&A) -> A>,
}

#[derive(Clone, PartialEq, Eq, Debug)]
/// Errors that can occur while constructing groups via [`Group::new`].
pub enum GroupError<A> {
    /// Tests are rejected.
    TestsRejected(Reason),
    /// x * (y * z) = (x * y) * z does not hold.
    NotAssociative(A, A, A),
    /// 1 * x = x does not hold.
    NotUnitaryLeft(A),
    /// x * 1 = x does not hold.
    NotUnitaryRight(A),
    /// x^(-1) * x = 1 does not hold.
    NotInvertible(A),
}
#[allow(clippy::missing_panics_doc)]

impl<A: Clone + Eq + std::fmt::Debug> Group<A> {
    /// Tries to construct a group from given operations.
    /// # Arguments
    /// * `op` - the group operation.
    /// * `id` - the identity element.
    /// * `inv` - the inverse operation.
    /// * `strategy` - a strategy that generates all elements of the group and only elements of the group.
    ///
    /// # Errors
    /// This function tests all the group properties before returning the given group. If any of the tests
    /// fail, a correspondent [`GroupError`] is returned.
    ///
    /// # Runtime
    /// This checks about 256 * 4 equations. If you need to construct a lot of small groups, consider other
    /// methods (that we do not have yet).
    pub fn new(
        op: Box<dyn Fn(&A, &A) -> A>,
        id: A,
        inv: Box<dyn Fn(&A) -> A>,
        strategy: &BoxedStrategy<A>,
    ) -> Result<Self, GroupError<A>> {
        let mut runner = TestRunner::new(proptest::test_runner::Config {
            failure_persistence: Some(Box::new(proptest::test_runner::FileFailurePersistence::Off)),
            ..proptest::test_runner::Config::default()
        });
        let assoc_result = runner.run(&(&strategy, &strategy, &strategy), |(x, y, z)| {
            assert_eq!(op(&x, &op(&y, &z)), op(&op(&x, &y), &z));
            Ok(())
        });
        if let Err(TestError::Abort(reason)) = assoc_result {
            return Err(GroupError::TestsRejected(reason));
        }
        if let Err(TestError::Fail(_, (x, y, z))) = assoc_result {
            return Err(GroupError::NotAssociative(x, y, z));
        }
        runner = TestRunner::new(proptest::test_runner::Config {
            failure_persistence: Some(Box::new(proptest::test_runner::FileFailurePersistence::Off)),
            ..proptest::test_runner::Config::default()
        });
        let unit_left_result = runner.run(&strategy, |x| {
            assert_eq!(op(&id, &x), x);
            Ok(())
        });
        if let Err(TestError::Abort(reason)) = unit_left_result {
            return Err(GroupError::TestsRejected(reason));
        }
        if let Err(TestError::Fail(_, x)) = unit_left_result {
            return Err(GroupError::NotUnitaryLeft(x));
        }
        runner = TestRunner::new(proptest::test_runner::Config {
            failure_persistence: Some(Box::new(proptest::test_runner::FileFailurePersistence::Off)),
            ..proptest::test_runner::Config::default()
        });
        let unit_right_result = runner.run(&strategy, |x| {
            assert_eq!(op(&x, &id), x);
            Ok(())
        });
        if let Err(TestError::Abort(reason)) = unit_right_result {
            return Err(GroupError::TestsRejected(reason));
        }
        if let Err(TestError::Fail(_, x)) = unit_right_result {
            return Err(GroupError::NotUnitaryRight(x));
        }
        runner = TestRunner::new(proptest::test_runner::Config {
            failure_persistence: Some(Box::new(proptest::test_runner::FileFailurePersistence::Off)),
            ..proptest::test_runner::Config::default()
        });
        let inv_left_result = runner.run(&strategy, |x| {
            assert_eq!(op(&inv(&x), &x), id);
            Ok(())
        });
        if let Err(TestError::Abort(reason)) = inv_left_result {
            return Err(GroupError::TestsRejected(reason));
        }
        if let Err(TestError::Fail(_, x)) = inv_left_result {
            return Err(GroupError::NotInvertible(x));
        }
        Ok(Self {
            op_fun: op,
            id_val: id,
            inv_fun: inv,
        })
    }
}

/// [`Group`]s are [`GroupLike`], in some sense they are even the free implementation.
impl<A: Clone> GroupLike<A> for Group<A> {
    fn op(&self, x: &A, y: &A) -> A {
        (self.op_fun)(x, y)
    }

    fn inv(&self, x: &A) -> A {
        (self.inv_fun)(x)
    }

    fn id(&self) -> A {
        self.id_val.clone()
    }
}

/// Finitely generated groups. These are [`Group`]s equipped with a finite collection of generators.
pub struct FinitelyGeneratedGroup<A> {
    group: Group<A>,
    generators: Vec<A>,
}

/// Finite groups. These are meant to be [`FinitelyGeneratedGroup`]s who are known to be finite,
/// however there are no uses yet.
pub struct FiniteGroup<A> {
    fin_gen_group: FinitelyGeneratedGroup<A>,
}

impl<A> From<FinitelyGeneratedGroup<A>> for Group<A> {
    fn from(value: FinitelyGeneratedGroup<A>) -> Self {
        value.group
    }
}

impl<A> From<FiniteGroup<A>> for FinitelyGeneratedGroup<A> {
    fn from(value: FiniteGroup<A>) -> Self {
        value.fin_gen_group
    }
}

impl<A> From<FiniteGroup<A>> for Group<A> {
    fn from(value: FiniteGroup<A>) -> Self {
        value.fin_gen_group.group
    }
}

impl<A> GroupLike<A> for FiniteGroup<A>
where
    A: Clone,
{
    fn op(&self, x: &A, y: &A) -> A {
        (*self.fin_gen_group.group.op_fun)(x, y)
    }

    fn inv(&self, x: &A) -> A {
        (*self.fin_gen_group.group.inv_fun)(x)
    }

    fn id(&self) -> A {
        self.fin_gen_group.group.id_val.clone()
    }
}

/// Iterator for acquiring all elements of finite groups.
struct FiniteGroupIter<'a, A> {
    elems: HashSet<A>,
    queue: VecDeque<A>,
    grp: &'a FiniteGroup<A>
}

impl<'a, A> Iterator for FiniteGroupIter<'a, A> where A: Clone + Eq + std::hash::Hash {
    type Item = A;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            let Some(x) = self.queue.pop_front() else { return None; };
            if self.elems.contains(&x) {
                continue;
            }
            self.elems.insert(x.clone());
            self.queue.extend(self.grp.fin_gen_group.generators.iter().map(|s| self.grp.op(&x, s)));
            return Some(x);
        }

    }
}

/// [`FiniteGroup`]s are [`FiniteGroupLike`]. Note that the elements of [`FiniteGroup`]s are not known in advance.
impl<A> FiniteGroupLike<A> for FiniteGroup<A>
where
    A: Clone + Eq + std::hash::Hash + PartialEq,
{
    /// Compute all elements of a [`FiniteGroup`] via their generators.
    /// # Runtime
    /// O(ord(self)), necessarily.
    fn all_elements(&self) -> impl Iterator<Item = A> {
        FiniteGroupIter {
            elems: HashSet::new(),
            queue: VecDeque::from([self.id()]),
            grp: self
        }
    }
}

impl<A: Clone> GroupLike<A> for FinitelyGeneratedGroup<A> {
    fn op(&self, x: &A, y: &A) -> A {
        (self.group.op_fun)(x, y)
    }

    fn inv(&self, x: &A) -> A {
        (self.group.inv_fun)(x)
    }

    fn id(&self) -> A {
        self.group.id_val.clone()
    }
}
mod test {
    #[allow(unused_imports)]
    use super::*;

    #[test]
    fn elems_mod_5() {
        let grp_mod_5: Group<i8> = Group {
            op_fun: Box::new(|x, y| (x + y) % 5),
            id_val: 0,
            inv_fun: Box::new(|x| (-x) % 5),
        };
        let finite_grp_mod_5: FiniteGroup<i8> = FiniteGroup {
            fin_gen_group: FinitelyGeneratedGroup {
                group: grp_mod_5,
                generators: vec![1],
            },
        };
        assert!(finite_grp_mod_5.all_elements().collect::<Vec<_>>() == vec![0, 1, 2, 3, 4]);
    }
    #[test]
    fn elems_sym_3() {
        let grp_sym_3: Group<[usize; 3]> = Group {
            op_fun: Box::new(|x, y| [x[y[0]], x[y[1]], x[y[2]]]),
            id_val: [0, 1, 2],
            inv_fun: Box::new(|x| *x), // TODO
        };
        let finite_grp_sym_3: FiniteGroup<[usize; 3]> = FiniteGroup {
            fin_gen_group: FinitelyGeneratedGroup {
                group: grp_sym_3,
                generators: vec![[1, 0, 2], [2, 1, 0]],
            },
        };
        assert_eq!(finite_grp_sym_3.order(), BigUint::from(6_u8));
    }

    #[test]
    fn group_refuse_not_associative() {
        let g = Group::new(
            Box::new(|x: &i32, y: &i32| x.saturating_sub(*y) as i32),
            0,
            Box::new(|x| -*x),
            &proptest::num::i32::ANY.boxed(),
        );
        match g {
            Err(super::GroupError::NotAssociative(_, _, _)) => (),
            _ => panic!(),
        }
    }

    #[test]
    fn group_refuse_not_left_unit() {
        let g: Result<Group<[usize; 3]>, _> = Group::new(
            Box::new(|x: &[usize; 3], y| [x[y[0]], x[y[1]], x[y[2]]]),
            [0, 1, 0],
            Box::new(|x| *x),
            &proptest::sample::select(vec![[0, 1, 0], [0, 2, 0], [0, 0, 0]]).boxed(),
        );
        match g {
            Err(super::GroupError::NotUnitaryLeft(_)) => (),
            _ => panic!(),
        }
    }

    #[test]
    fn group_refuse_not_right_unit() {
        let g: Result<Group<[usize; 3]>, _> = Group::new(
            Box::new(|y: &[usize; 3], x| [x[y[0]], x[y[1]], x[y[2]]]),
            [0, 1, 0],
            Box::new(|x| *x),
            &proptest::sample::select(vec![[0, 1, 0], [0, 2, 0], [0, 0, 0]]).boxed(),
        );
        match g {
            Err(super::GroupError::NotUnitaryRight(_)) => (),
            _ => panic!(),
        }
    }
    #[test]
    fn group_refuse_not_inv() {
        let g: Result<Group<[usize; 3]>, _> = Group::new(
            Box::new(|x: &[usize; 3], y| [x[y[0]], x[y[1]], x[y[2]]]),
            [0, 1, 2],
            Box::new(|x| *x),
            &proptest::array::uniform3(0..3usize).boxed(),
        );
        match g {
            Err(super::GroupError::NotInvertible(_)) => (),
            _ => panic!(),
        }
    }
}
