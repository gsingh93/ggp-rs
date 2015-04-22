//! This module literals in a GDL description such that all variables in a negative literal (i.e. a
//! `distinct` or `not` literal) have been seen in positive literals occurring before that
//! `negative` literal. The resulting GDL should be semantically equivalent. To see why this is
//! necessary, see section 13.6 [here](http://logic.stanford.edu/ggp/chapters/chapter_13.html). For
//! an example test case of where this makes a difference, see the `test_beginning_distinct` test
//! case in this file.

use std::collections::HashSet;

use prover::deorer;
use gdl::{Description, Rule, Variable, Literal, Term};
use gdl::Clause::RuleClause;
use gdl::Literal::{OrLit, NotLit, DistinctLit, RelLit};
use gdl::Term::{VarTerm, FuncTerm};

/// Reorders a game description such that all negative literals occur after all their variables
/// have been seen in a positive literal
pub fn reorder(desc: Description) -> Description {
    let desc = deorer::deor(desc);

    let mut new_clauses = Vec::new();
    for clause in desc.clauses {
        match clause {
            RuleClause(r) => {
                new_clauses.push(reorder_rule(r).into());
            }
            _ => new_clauses.push(clause)
        }
    }
    Description::new(new_clauses)
}

fn reorder_rule(mut r: Rule) -> Rule {
    loop {
        match find_neg_lit_index(&*r.body) {
            Some(index) => {
                let swap_index = find_candidate_index(&*r.body, &r.body[index])
                    .expect("No candidate index found");
                let body = &mut *r.body;
                body.swap(index, swap_index);
            }
            None => break
        }
    }
    r
}

fn find_neg_lit_index(body: &[Literal]) -> Option<usize> {
    let mut seen_vars = HashSet::new();
    for (i, lit) in body.iter().enumerate() {
        match lit {
            l @ &DistinctLit(_) | l @ &NotLit(_) => {
                if !seen_all_vars(&seen_vars, l) {
                    return Some(i);
                }
            }
            l @ &RelLit(_) => {
                seen_vars.extend(get_vars(l));
            }
            &OrLit(_) => panic!("Or literals were removed"),
            _ => ()
        }
    }
    None
}

fn find_candidate_index(body: &[Literal], neg_lit: &Literal) -> Option<usize> {
    let mut seen_vars = HashSet::new();
    for (i, lit) in body.iter().enumerate() {
        match lit {
            l @ &RelLit(_) => {
                seen_vars.extend(get_vars(l));
                if seen_all_vars(&seen_vars, neg_lit) {
                    return Some(i)
                }
            },
            &OrLit(_) => panic!("Or literals were removed"),
            _ => ()
        }
    }
       None
}

fn get_vars(l: &Literal) -> Vec<Variable> {
    let mut res = Vec::new();
    match l {
        &RelLit(ref r) => {
            for term in r.args.iter() {
                res.extend(get_vars_from_term(term));
            }
            res
        },
        &NotLit(ref not) => get_vars(&not.lit),
        &DistinctLit(ref distinct) => {
            res.extend(get_vars_from_term(&distinct.term1));
            res.extend(get_vars_from_term(&distinct.term2));
            res
        },
        &OrLit(_) => panic!("Or literals were removed"),
        _ => res
    }
}

fn get_vars_from_term(t: &Term) -> Vec<Variable> {
    match t {
        &VarTerm(ref v) => vec![(*v).clone()],
        &FuncTerm(ref f) => {
            let mut res = Vec::new();
            for t in f.args.iter() {
                res.extend(get_vars_from_term(t));
            }
            res
        }
        _ => Vec::new()
    }
}

fn seen_all_vars(seen_vars: &HashSet<Variable>, l: &Literal) -> bool {
    let vars = get_vars(l);
    for var in vars {
        if !seen_vars.contains(&var) {
            return false;
        }
    }
    true
}

#[cfg(test)]
mod test {
    use {gdl, State, Role};
    use super::reorder;
    use prover::Prover;
    use prover::query_builder;

    #[test]
    fn test_distinct() {
        let desc = gdl::parse("(<= p (distinct ?a ?b) (q ?a ?b))");
        let expected = gdl::parse("(<= p (q ?a ?b) (distinct ?a ?b))");
        assert_eq!(reorder(desc), expected);
    }

    #[test]
    fn test_not_function() {
        let desc = gdl::parse("(<= p (not (foo (bar ?a))) (q ?a))");
        let expected = gdl::parse("(<= p (q ?a) (not (foo (bar ?a))))");
        assert_eq!(reorder(desc), expected);
   }

    #[test]
    fn test_not() {
        let desc = gdl::parse("(<= p (not (foo ?a)) (q ?a))");
        let expected = gdl::parse("(<= p (q ?a) (not (foo ?a)))");
        assert_eq!(reorder(desc), expected);
    }

    #[test]
    fn test_multiple_swap() {
        let desc = gdl::parse("(<= p (not (bar ?a)) (not (foo ?a ?b)) (q ?a) (distinct ?a ?b) \
                               (q ?b) (q ?c))");
        let expected = gdl::parse("(<= p (q ?a) (q ?b) (not (bar ?a)) (distinct ?a ?b) \
                                   (not (foo ?a ?b)) (q ?c))");
        assert_eq!(reorder(desc), expected);
    }

    #[test]
    fn test_no_move() {
        let desc = gdl::parse("(<= p (q ?a) (not (foo ?a)))");
        assert_eq!(reorder(desc.clone()), desc);

        let desc = gdl::parse("(<= p (q ?a) (distinct ?a))");
        assert_eq!(reorder(desc.clone()), desc);
    }

    #[test]
    fn test_beginning_distinct() {
        let gdl = "(role you) \
                   (<= (foo ?a ?b) \
                     (distinct ?a ?b) \
                     (p ?a) \
                     (q ?b)) \
                   (p a) \
                   (p b) \
                   (q a) \
                   (q b) \
                   (<= (legal you (do ?a ?b)) \
                     (foo ?a ?b)) \
                   (next win) \
                   (<= terminal \
                     (true win)) \
                   (goal you 100)";
        let desc = gdl::parse(gdl);
        let prover = Prover::new(desc);
        let moves =
            prover.ask(query_builder::legal_query(&Role::new("you")), State::new()).into_moves();
        // Without the reordering, there are four legal moves, which is incorrect
        assert_eq!(moves.len(), 2);
    }
}
