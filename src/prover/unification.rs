use prover::substitution::Substitution;

use gdl::{Variable, Term, Relation, Function};
use gdl::Term::{VarTerm, ConstTerm, FuncTerm};

/// Unifies relations `r1` and `r2`, returning a `Substitution` mapping one into the other if such
/// a substitution exists, otherwise returns `None`.
pub fn unify(r1: Relation, r2: Relation) -> Option<Substitution> {
    let x = Function::new(r1.name, r1.args).into();
    let y = Function::new(r2.name, r2.args).into();
    unify_term(x, y, Substitution::new())
}

fn unify_term(x: Term, y: Term, theta: Substitution) -> Option<Substitution> {
    if x == y {
        return Some(theta)
    }

    match (x, y) {
        (VarTerm(v), y) => unify_variable(v, y, theta),
        (x, VarTerm(v)) => unify_variable(v, x, theta),
        (ConstTerm(_), ConstTerm(_)) => None,
        (FuncTerm(f1), FuncTerm(f2)) => {
            match unify_term(f1.name.into(), f2.name.into(), theta) {
                Some(mut theta) => {
                    assert_eq!(f1.args.len(), f2.args.len());
                    for (arg1, arg2) in f1.args.into_iter().zip(f2.args.into_iter()) {
                        match unify_term(arg1, arg2, theta) {
                            Some(theta_prime) => theta = theta_prime,
                            None => return None
                        }
                    }
                    Some(theta)
                },
                None => None
            }
        },
        _ => None
    }
}

fn unify_variable(x: Variable, y: Term, mut theta: Substitution) -> Option<Substitution> {
    // TODO: I'm not sure if these two if statements are even necessary
    if let Some(t) = theta.get(&x).cloned() {
        return unify_term(t, y, theta);
    }
    if let VarTerm(ref v) = y {
        if let Some(t) = theta.get(&v).cloned() {
            return unify_term(x.into(), t, theta)
        }
    }

    // Neither x nor y were found in theta
    theta.insert(x, y);
    Some(theta)
}

#[cfg(test)]
mod test {
    use std::collections::BTreeMap;

    use gdl::{self, Variable, Constant, Function};
    use prover::substitution::Substitution;
    use util::test::to_relation;

    use super::unify;

    #[test]
    fn test_unify() {
        let a = to_relation(gdl::parse("(legal white ?l)"));
        let b = to_relation(gdl::parse("(legal ?p (reduce ?x ?n))"));
        let c = to_relation(gdl::parse("(reduce ?x ?n)"));

        let mut map = BTreeMap::new();
        map.insert(Variable::new("p"), Constant::new("white").into());
        map.insert(Variable::new("l"), Function::new(c.name, c.args).into());
        let theta = Substitution { mapping: map };
        assert_eq!(unify(a, b).unwrap(), theta);
    }
}
