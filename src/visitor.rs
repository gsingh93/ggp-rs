use gdl::{Description, Sentence, Proposition, Relation, Literal, Or, Not, Distinct, Function, Rule,
          Variable, Constant, Clause, Term};
use gdl::Clause::{RuleClause, SentenceClause};
use gdl::Sentence::{PropSentence, RelSentence};
use gdl::Term::{ConstTerm, FuncTerm, VarTerm};
use gdl::Literal::{OrLit, NotLit, DistinctLit, PropLit, RelLit};

pub trait Visitor {
    fn visit_clause(&self, _: &Clause) {}

    fn visit_rule(&self, _: &Rule) {}

    fn visit_sentence(&self, _: &Sentence) {}

    fn visit_proposition(&self, _: &Proposition) {}

    fn visit_relation(&self, _: &Relation) {}

    fn visit_literal(&self, _: &Literal) {}

    fn visit_term(&self, _: &Term) {}

    fn visit_constant(&self, _: &Constant) {}

    fn visit_or(&self, _: &Or) {}

    fn visit_not(&self, _: &Not) {}

    fn visit_distinct(&self, _: &Distinct) {}

    fn visit_variable(&self, _: &Variable) {}

    fn visit_function(&self, _: &Function) {}
}

pub fn visit<V: Visitor>(desc: &Description, visitor: &mut V) {
    for clause in desc.clauses.iter() {
        visit_clause(clause, visitor);
    }
}

fn visit_clause<V: Visitor>(clause: &Clause, visitor: &mut V) {
    match clause {
        &RuleClause(ref r) => visit_rule(r, visitor),
        &SentenceClause(ref s) => visit_sentence(s, visitor)
    }
    visitor.visit_clause(clause);
}

fn visit_rule<V: Visitor>(rule: &Rule, visitor: &mut V) {
    visit_sentence(&rule.head, visitor);
    for l in rule.body.iter() {
        visit_literal(l, visitor);
    }
    visitor.visit_rule(rule);
}

fn visit_sentence<V: Visitor>(sentence: &Sentence, visitor: &mut V) {
    match sentence {
        &PropSentence(ref p) => visit_proposition(p, visitor),
        &RelSentence(ref r) => visit_relation(r, visitor)
    }
    visitor.visit_sentence(sentence);
}

fn visit_proposition<V: Visitor>(proposition: &Proposition, visitor: &mut V) {
    visit_constant(&proposition.name, visitor);
    visitor.visit_proposition(proposition)
}

fn visit_relation<V: Visitor>(relation: &Relation, visitor: &mut V) {
    visit_constant(&relation.name, visitor);
    for t in relation.args.iter() {
        visit_term(t, visitor)
    }
    visitor.visit_relation(relation)
}

fn visit_literal<V: Visitor>(literal: &Literal, visitor: &mut V) {
    match literal {
        &OrLit(ref or) => visit_or(or, visitor),
        &NotLit(ref not) => visit_not(not, visitor),
        &DistinctLit(ref distinct) => visit_distinct(distinct, visitor),
        &RelLit(ref rel) => visit_relation(rel, visitor),
        &PropLit(ref prop) => visit_proposition(prop, visitor)
    }
    visitor.visit_literal(literal);
}

fn visit_term<V: Visitor>(term: &Term, visitor: &mut V) {
    match term {
        &ConstTerm(ref c) => visit_constant(c, visitor),
        &FuncTerm(ref f) => visit_function(f, visitor),
        &VarTerm(ref v) => visit_variable(v, visitor)
    }
    visitor.visit_term(term);
}

fn visit_constant<V: Visitor>(constant: &Constant, visitor: &mut V) {
    visitor.visit_constant(constant);
}

fn visit_or<V: Visitor>(or: &Or, visitor: &mut V) {
    for l in or.lits.iter() {
        visit_literal(l, visitor);
    }
    visitor.visit_or(or);
}

fn visit_not<V: Visitor>(not: &Not, visitor: &mut V) {
    visit_literal(&not.lit, visitor);
    visitor.visit_not(not);
}

fn visit_distinct<V: Visitor>(distinct: &Distinct, visitor: &mut V) {
    visit_term(&distinct.term1, visitor);
    visit_term(&distinct.term2, visitor);
    visitor.visit_distinct(distinct);
}

fn visit_variable<V: Visitor>(variable: &Variable, visitor: &mut V) {
    visit_constant(&variable.name, visitor);
    visitor.visit_variable(variable);
}

fn visit_function<V: Visitor>(function: &Function, visitor: &mut V) {
    visit_constant(&function.name, visitor);
    for t in function.args.iter() {
        visit_term(t, visitor)
    }
    visitor.visit_function(function)
}
