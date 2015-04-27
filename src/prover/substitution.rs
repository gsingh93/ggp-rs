use std::collections::BTreeMap;

use gdl::{Literal, Variable, Constant, Term, Function};
use gdl::Term::{VarTerm, ConstTerm, FuncTerm};

use gdl_parser::visitor::{self, Visitor};

/// A mapping from `Variable`s to `Term`s
#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub struct Substitution {
    pub mapping: BTreeMap<Variable, Term>
}

impl Substitution {
    pub fn new() -> Substitution {
        Substitution { mapping: BTreeMap::new() }
    }

    pub fn substitute(&self, l: &Literal) -> Literal {
        let mut l = l.clone();
        let mut v = SubstitutionVisitor { theta: self };
        visitor::visit_literal(&mut l, &mut v);
        l
    }

    pub fn compose(&self, theta: Substitution) -> Substitution {
        let mut t = self.clone();
        for (k, v) in theta.mapping {
            t.insert(k, v);
        }
        t
    }

    pub fn insert(&mut self, v: Variable, t: Term) {
        self.mapping.insert(v, t);
    }

    pub fn get(&self, v: &Variable) -> Option<&Term> {
        self.mapping.get(v)
    }
}

/// A visitor that applies the substitution `theta` to all variables in a literal
struct SubstitutionVisitor<'a> {
    theta: &'a Substitution
}

impl<'a> SubstitutionVisitor<'a> {
    fn visit_function(&mut self, func: &mut Function) {
        for arg in func.args.iter_mut() {
            if let VarTerm(v) = (*arg).clone() {
                if let Some(t) = self.theta.get(&v) {
                    *arg = (*t).clone()
                }
            }
        }
    }
}

impl<'a> Visitor for SubstitutionVisitor<'a> {
    fn visit_term(&mut self, term: &mut Term) {
        let mut t2 = Constant::new("").into();
        let mut should_replace = false;
        match term {
            &mut VarTerm(ref v) => {
                if let Some(mut t) = self.theta.get(&v).cloned() {
                    should_replace = true;
                    while t2 != t {
                        t2 = t.clone();
                        self.visit_term(&mut t);
                    }
                }
            },
            &mut FuncTerm(ref mut f) => { self.visit_function(f); return },
            &mut ConstTerm(_) => return,
        }
        if should_replace {
            *term = t2;
        }
    }
}

#[cfg(test)]
mod test {
    use std::collections::BTreeMap;
    use gdl::{self, Variable, Constant, Function};
    use util::test::to_relation;
    use super::Substitution;

    #[test]
    fn test_substitute() {
        let a = to_relation(gdl::parse("(legal ?p ?m)")).into();
        let b = to_relation(gdl::parse("(legal white (reduce a 1))")).into();

        let mut mapping = BTreeMap::new();
        mapping.insert(Variable::new("p"), Constant::new("white").into());
        mapping.insert(Variable::new("m"),
                       Function::new("reduce",
                                     vec![Variable::new("R1").into(),
                                          Variable::new("R2").into()]).into());
        mapping.insert(Variable::new("R1"), Constant::new("a").into());
        mapping.insert(Variable::new("R2"), Constant::new("1").into());
        let theta = Substitution { mapping: mapping };

        assert_eq!(theta.substitute(&a), b);
    }
}
