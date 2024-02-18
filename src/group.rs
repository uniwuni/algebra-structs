use std::collections::HashSet;
use std::collections::VecDeque;
use num::BigInt;
use num::BigUint;
use num::bigint::ToBigInt;
use num::bigint::ToBigUint;
use num_traits::One;
use num_traits::Zero;
use proptest::prelude::*;
use proptest::test_runner::*;

pub trait GroupLike<A> {
    fn op(&self, x: &A, y: &A) -> A;
    fn id(&self) -> A;
    fn inv(&self, x: &A) -> A;
    fn power(&self, x: &A, n: i64) -> A where A: Clone {
        if n == 0 {
            self.id()
        } else if n < 0 {
            self.power(&self.inv(x), -n)
        } else {
            if n == 1 {
                x.clone()
            } else {
                if n % 2 == 0 {
                    self.power(&self.op(x, x), n / 2)
                } else {
                    self.op(x, &self.power(&self.op(x, x), n / 2))
                }
            }
        }
    }
    fn power_bigint(&self, x: &A, n: BigInt) -> A where A: Clone {
        if n == Zero::zero() {
            self.id()
        } else if n < Zero::zero() {
            self.power_bigint(&self.inv(x), (-1) * n)
        } else {
            if n == One::one() {
                x.clone()
            } else {
                if n.clone() % 2 == Zero::zero() {
                    self.power_bigint(&self.op(x, x), n / 2_i8.to_bigint().unwrap())
                } else {
                    self.op(x, &self.power_bigint(&self.op(x, x), n / 2_i8.to_bigint().unwrap()))
                }
            }
        }
    }
}

pub enum NNInf {
    Fin(BigUint),
    Inf
}

pub trait OrderGroupLike<A>: GroupLike<A> {
    fn order_of(&self, x: &A) -> NNInf;
}

pub trait ConjugacyGroupLike<A>: GroupLike<A> {
    /// search a with axa^(-1) = y
    fn are_conjugate(&self, x: &A, y: &A) -> Option<A>;
}

pub trait FiniteGroupLike<A>: GroupLike<A> {
    fn order(&self) -> BigUint {
        let all = self.all_elements();
        all.len().into()
    }
    fn all_elements(&self) -> HashSet<A>;
    fn bruteforce_order_of(&self, x: A) -> NNInf where A : Clone + PartialEq{
      let mut y = x.clone();
      let mut n: u64 = 0;
      while y != self.id() {
          y = self.op(&y,&x);
          n += 1;
      }
      NNInf::Fin(n.to_biguint().unwrap())
  }
}

pub struct Group<A> {
    op_fun: Box<dyn Fn(&A, &A) -> A>,
    id_val: A,
    inv_fun: Box<dyn Fn(&A) -> A>,
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub enum GroupError<A> {
    TestsRejected(Reason),
    /// x * (y * z) = (x * y) * z fails.
    NotAssociative(A, A, A),
    /// 1 * x = x fails.
    NotUnitaryLeft(A),
    /// x * 1 = x fails.
    NotUnitaryRight(A),
    /// x^(-1) * x = 1 fails.
    NotInvertibleLeft(A),
    /// x * x^(-1) = 1 fails.
    NotInvertibleRight(A),
}

impl<A: Clone + Eq + std::fmt::Debug> Group<A> {
    pub fn new(
        op: Box<dyn Fn(&A, &A) -> A>,
        id: A,
        inv: Box<dyn Fn(&A) -> A>,
        strategy: BoxedStrategy<A>,
    ) -> Result<Group<A>, GroupError<A>> {
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
        let inv_left_result = runner.run(&strategy, |x| {
            assert_eq!(op(&inv(&x), &x), id);
            Ok(())
        });
        if let Err(TestError::Abort(reason)) = inv_left_result {
            return Err(GroupError::TestsRejected(reason));
        }
        if let Err(TestError::Fail(_, x)) = inv_left_result {
            return Err(GroupError::NotInvertibleLeft(x));
        }
        let inv_right_result = runner.run(&strategy, |x| {
            assert_eq!(op(&inv(&x), &x), id);
            Ok(())
        });
        if let Err(TestError::Abort(reason)) = inv_right_result {
            return Err(GroupError::TestsRejected(reason));
        }
        if let Err(TestError::Fail(_, x)) = inv_right_result {
            return Err(GroupError::NotInvertibleRight(x));
        }
        return Ok(Group {
            op_fun: op,
            id_val: id,
            inv_fun: inv,
        });
    }
}

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

struct FinitelyGeneratedGroup<A> {
    group: Group<A>,
    generators: Vec<A>,
}

struct FiniteGroup<A> {
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

impl<A> FiniteGroupLike<A> for FiniteGroup<A>
where
    A: Clone + Eq + std::hash::Hash + PartialEq,
{
    fn all_elements(&self) -> HashSet<A> {
        let mut elems: HashSet<A> = HashSet::new();
        let mut queue: VecDeque<A> = VecDeque::from([self.id()]);
        while let Some(x) = queue.pop_front() {
            if elems.contains(&x) {
                continue;
            } else {
                elems.insert(x.clone());
                queue.extend(self.fin_gen_group.generators.iter().map(|s| self.op(&x, &s)));
            }
        }
        elems
    }
}

impl<A: Copy> GroupLike<A> for FinitelyGeneratedGroup<A> {
    fn op(&self, x: &A, y: &A) -> A {
        (self.group.op_fun)(x, y)
    }

    fn inv(&self, x: &A) -> A {
        (self.group.inv_fun)(x)
    }

    fn id(&self) -> A {
        self.group.id_val
    }
}

mod test {
    use std::collections::HashSet;

    use num::BigUint;

    use crate::group::FiniteGroupLike;

    use super::{FiniteGroup, FinitelyGeneratedGroup, Group};

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
        assert!(finite_grp_mod_5.all_elements() == HashSet::from([0, 1, 2, 3, 4]));
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
        assert_eq!(finite_grp_sym_3.order(), BigUint::from(6 as u8));
    }
}
