use gdl::{Description, Rule, Literal, Not};
use gdl::Clause::RuleClause;
use gdl::Literal::{OrLit, NotLit};

use self::ExpansionResult::{ExpandedOr, ExpandedNot, NoExpansion};

pub fn deor(desc: Description) -> Description {
    let mut new_clauses = Vec::new();
    for clause in desc.clauses {
        match clause {
            RuleClause(r) => {
                let rules = deor_rule(r);
                for rule in rules {
                    new_clauses.push(rule.into());
                }
            }
            _ => new_clauses.push(clause)
        }
    }
    Description::new(new_clauses)
}

fn deor_rules(rules: Vec<Rule>) -> Vec<Rule> {
    let mut res = Vec::new();
    for rule in rules {
        res.extend(deor_rule(rule));
    }
    res
}

fn deor_rule(r: Rule) -> Vec<Rule> {
    let rule = r.clone();
    for (i, lit) in r.body.into_iter().enumerate() {
        match expand_first_or(lit) {
            ExpandedOr(expanded_lit) => {
                let mut new_rules = Vec::new();
                for l in expanded_lit {
                    let mut new_rule = rule.clone();
                    new_rule.body[i] = l;
                    new_rules.push(new_rule);
                }
                return deor_rules(new_rules);
            }
            ExpandedNot(nots) => {
                let mut new_rule = rule.clone();
                new_rule.body.swap_remove(i);
                for not in nots {
                    new_rule.body.push(not.into());
                }
                return deor_rules(vec![new_rule]);
            }
            NoExpansion => ()
        }
    }

    // If no literal was expanded (rule contains no ORs), return original rule
    vec![rule]
}

enum ExpansionResult {
    ExpandedOr(Vec<Literal>),
    ExpandedNot(Vec<Not>),
    NoExpansion
}

fn expand_first_or(lit: Literal) -> ExpansionResult {
    fn recurse(lit: Literal, num_nots: &mut u32) -> ExpansionResult {
        match lit {
            OrLit(or) => {
                let mut res = Vec::new();
                for l in or.lits {
                    res.push(l);
                }
                return ExpandedOr(res);
            }
            NotLit(not) => {
                let mut res = Vec::new();
                *num_nots += 1;
                match recurse(*not.lit, num_nots) {
                    ExpandedOr(expanded_lit) => {
                        if *num_nots % 2 == 1 {
                            for l in expanded_lit {
                                res.push(Not::new(Box::new(l)));
                            }
                            return ExpandedNot(res);
                        } else {
                            return ExpandedOr(expanded_lit);
                        }
                    }
                    res => return res
                }
            }
            _ => NoExpansion
        }
    }
    recurse(lit, &mut 0)
}

#[cfg(test)]
mod test {
    use gdl;
    use super::deor;

    #[test]
    fn test_single_or() {
        let desc = gdl::parse("(<= p (or a b c))");
        let expected = gdl::parse("(<= p a) (<= p b) (<= p c)");
        assert_eq!(deor(desc), expected);
    }

    #[test]
    fn test_not() {
        let desc = gdl::parse("(<= p (not (or a b)))");
        let expected = gdl::parse("(<= p (not a) (not b))");
        assert_eq!(deor(desc), expected);
    }

    #[test]
    fn test_odd_nested_not() {
        let desc = gdl::parse("(<= p (not (not (not (or a b)))))");
        let expected = gdl::parse("(<= p (not a) (not b))");
        assert_eq!(deor(desc), expected);
    }

    #[test]
    fn test_even_nested_not() {
        let desc = gdl::parse("(<= p (not (not (or a b))))");
        let expected = gdl::parse("(<= p a) (<= p b)");
        assert_eq!(deor(desc), expected);
    }

    #[test]
    fn test_multiple_or() {
        let desc = gdl::parse("(<= p (or a b) (or d e))");
        let expected = gdl::parse("(<= p a d) (<= p a e) (<= p b d) (<= p b e)");
        assert_eq!(deor(desc), expected);
    }

    #[test]
    fn test_nested_multiple_or() {
        let desc = gdl::parse("(<= p (or (or a b) (or c (or d e))) (or (or f g) h)) \
                               (<= q (or a b))");
        let expected = gdl::parse("(<= p a f) (<= p a g) (<= p a h) \
                                   (<= p b f) (<= p b g) (<= p b h) \
                                   (<= p c f) (<= p c g) (<= p c h) \
                                   (<= p d f) (<= p d g) (<= p d h) \
                                   (<= p e f) (<= p e g) (<= p e h) \
                                   (<= q a) (<= q b)");
        assert_eq!(deor(desc), expected);
    }
}
