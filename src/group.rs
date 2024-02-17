use std::collections::HashSet;
use std::collections::VecDeque;

trait GroupLike<A: Copy> {
    fn op(&self, x: A, y: A) -> A;
    fn id(&self) -> A;
    fn inv(&self, x: A) -> A;
    fn power(&self, x: A, n: i64) -> A {
        if n == 0 { self.id() }
        else if n < 0 {
            self.power(self.inv(x), -n)
        }
        else {
            if n == 1 {
                x
            } else {
                if n % 2 == 0 {
                    self.power(self.op(x,x), n / 2)
                } else {
                    self.op(x,self.power(self.op(x,x), n / 2))
                }
            }
        }
    }
}

trait FiniteGroupLike<A : Copy>: GroupLike<A> {
    fn order(&self) -> usize {
        let all = self.all_elements();
        all.len()
    }
    fn all_elements(&self) -> HashSet<A>;
}

struct Group<A> {
    op_fun: Box<dyn Fn(A, A) -> A>,
    id_val: A,
    inv_fun: Box<dyn Fn(A) -> A>,
}

impl<A: Copy> GroupLike<A> for Group<A> {
    fn op(&self, x: A, y: A) -> A {
        (self.op_fun)(x, y)
    }

    fn inv(&self, x: A) -> A {
        (self.inv_fun)(x)
    }

    fn id(&self) -> A {
        self.id_val
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

impl<A> GroupLike<A> for FiniteGroup<A> where A: Copy {
    fn op(&self, x: A, y: A) -> A {
        (*self.fin_gen_group.group.op_fun)(x, y)
    }

    fn inv(&self, x: A) -> A {
        (*self.fin_gen_group.group.inv_fun)(x)
    }

    fn id(&self) -> A {
        self.fin_gen_group.group.id_val
    }
}

impl<A> FiniteGroupLike<A> for FiniteGroup<A> where A: Copy + Eq + std::hash::Hash + PartialEq {
    fn all_elements(&self) -> HashSet<A> {
        let mut elems: HashSet<A> = HashSet::new();
        let mut queue: VecDeque<A> = VecDeque::from([self.id()]);
        while let Some(x) = queue.pop_front() {
            if elems.contains(&x) {
                continue;
            } else {
                elems.insert(x);
                queue.extend(self.fin_gen_group.generators.iter().map(|s| self.op(x,*s)));
            }
        }
        elems
    }
}

impl<A: Copy> GroupLike<A> for FinitelyGeneratedGroup<A> {
    fn op(&self, x: A, y: A) -> A {
        (self.group.op_fun)(x, y)
    }

    fn inv(&self, x: A) -> A {
        (self.group.inv_fun)(x)
    }

    fn id(&self) -> A {
        self.group.id_val
    }
}

mod test {
    use std::collections::HashSet;

    use crate::group::FiniteGroupLike;

    use super::{Group, FiniteGroup, FinitelyGeneratedGroup};

    #[test]
    fn elems_mod_5() {
        let grp_mod_5: Group<i8> = Group {
            op_fun: Box::new(|x,y| (x + y) % 5),
            id_val: 0,
            inv_fun: Box::new(|x| (- x) % 5),
        };
        let finite_grp_mod_5: FiniteGroup<i8> = FiniteGroup {
            fin_gen_group: FinitelyGeneratedGroup {
                group: grp_mod_5,
                generators: vec![1],
            },
        };
        assert!(finite_grp_mod_5.all_elements() == HashSet::from([0,1,2,3,4]));
    }
    #[test]
    fn elems_sym_3() {
        let grp_sym_3: Group<[usize;3]> = Group {
            op_fun: Box::new(|x,y| [x[y[0]], x[y[1]], x[y[2]]]),
            id_val: [0,1,2],
            inv_fun: Box::new(|x| x), // TODO
        };
        let finite_grp_sym_3: FiniteGroup<[usize;3]> = FiniteGroup {
            fin_gen_group: FinitelyGeneratedGroup {
                group: grp_sym_3,
                generators: vec![[1,0,2],[2,1,0]],
            },
        };
        assert_eq!(finite_grp_sym_3.order(), 6);
    }
}
