//! The `deorer` module transforms a game description into a semantically equivalent game
//! description with all `or` literals removed.

use gdl::{Description, Rule, Literal, Not};
use gdl::Clause::RuleClause;
use gdl::Literal::{OrLit, NotLit};

use self::ExpansionResult::{ExpandedOr, ExpandedNot, NoExpansion};

/// Remove all `or` literals from the game description
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

/// Remove the `or` literals from each rule in `rules` and return the new rules
fn deor_rules(rules: Vec<Rule>) -> Vec<Rule> {
    let mut res = Vec::new();
    for rule in rules {
        res.extend(deor_rule(rule));
    }
    res
}

/// Remove the `or` literals from rule `r` and return the new rules. For example, the rule
/// (<= p (or a b)) would turn into the two rules (<= p a) and (<= p b). The rule
/// (<= p (not (or a b))) should return the single rule (<= p (not a) (not b)).
fn deor_rule(r: Rule) -> Vec<Rule> {
    let rule = r.clone();

    // Expand each literal in the body of the rule
    for (i, lit) in r.body.into_iter().enumerate() {
        // Find the first `or` in the literal and expand it into multiple rules
        match expand_first_or(lit) {
            // If we find an `or` before any `not`s, we make one new rule for each argument
            // to the `or`
            ExpandedOr(expanded_lit) => {
                let mut new_rules = Vec::new();
                for l in expanded_lit {
                    let mut new_rule = rule.clone();
                    new_rule.body[i] = l;
                    new_rules.push(new_rule);
                }
                return deor_rules(new_rules);
            }
            // If we find a `not` then an `or`, we make one new rule using De Morgan's law
            ExpandedNot(nots) => {
                let mut new_rule = rule.clone();
                new_rule.body.swap_remove(i);
                for not in nots {
                    new_rule.body.push(not.into());
                }
                return deor_rules(vec![new_rule]);
            }
            // There were no `or`s in the literal
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
                // We keep track of how many `not`s we've seen and recurse until there are no more
                // literals or we find an `or`
                let mut res = Vec::new();
                *num_nots += 1;
                match recurse(*not.lit, num_nots) {
                    ExpandedOr(expanded_lit) => {
                        if *num_nots % 2 == 1 {
                            // The number of `not`s is odd, so we must apply De Morgan's law once
                            for l in expanded_lit {
                                res.push(Not::new(Box::new(l)));
                            }
                            return ExpandedNot(res);
                        } else {
                            // The number of `not`s, is even, so they cancel each other out
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
