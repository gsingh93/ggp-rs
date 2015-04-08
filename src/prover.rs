use std::collections::{HashSet, HashMap, VecDeque};

use game_manager::State;
use gdl::{Description, Sentence, Proposition, Relation, Move, Score, Literal, Or, Not, Distinct,
          Variable, Constant, Term, Function, Rule};
use gdl::Clause::{SentenceClause, RuleClause};
use gdl::Literal::{OrLit, NotLit, DistinctLit, PropLit, RelLit};
use gdl::Sentence::{PropSentence, RelSentence};
use gdl::Term::{VarTerm, ConstTerm, FuncTerm};

use visitor::{self, Visitor};

use std::mem;

struct SubstitutionVisitor<'a> {
    theta: &'a Substitution
}

impl<'a> Visitor for SubstitutionVisitor<'a> {
    fn visit_relation(&mut self, rel: &mut Relation) {
        for arg in rel.args.iter_mut() {
            let mut tmp: Term = Constant::new("").into();
            mem::swap(arg, &mut tmp);
            self.set_term(tmp, arg);
        }
    }

    fn visit_distinct(&mut self, distinct: &mut Distinct) {
        let mut tmp: Term = Constant::new("").into();
        mem::swap(&mut distinct.term1, &mut tmp);
        self.set_term(tmp, &mut distinct.term1);
    }

    fn visit_function(&mut self, func: &mut Function) {
        for arg in func.args.iter_mut() {
            let mut tmp: Term = Constant::new("").into();
            mem::swap(arg, &mut tmp);
            self.set_term(tmp, arg);
        }
    }
}

impl<'a> SubstitutionVisitor<'a> {
    fn set_term(&self, term: Term, loc: &mut Term) {
        if let VarTerm(v) = term {
            if let Some(t) = self.theta.get(&v) {
                *loc = (*t).clone();
            }
        }
    }
}

#[derive(Clone)]
struct Substitution {
    mapping: HashMap<Variable, Term>
}

impl Substitution {
    fn new() -> Substitution {
        Substitution { mapping: HashMap::new() }
    }

    fn substitute(&self, l: &Literal) -> Literal {
        let mut l = l.clone();
        let mut v = SubstitutionVisitor { theta: self };
        visitor::visit_literal(&mut l, &mut v);
        l
    }

    fn compose(&self, theta: Substitution) -> Substitution {
        let mut t = self.clone();
        for (k, v) in theta.mapping {
            t.insert(k, v);
        }
        t
    }

    fn insert(&mut self, v: Variable, t: Term) {
        self.mapping.insert(v, t);
    }

    fn get(&self, v: &Variable) -> Option<&Term> {
        self.mapping.get(v)
    }
}

struct VarRenamer {
    id: u32
}

impl VarRenamer {
    fn new() -> VarRenamer {
        VarRenamer { id: 0 }
    }

    fn rename(&mut self, r: &Rule) -> Rule {
        let mut r = r.clone();
        let mut v = RenamingVisitor::new(self);
        visitor::visit_rule(&mut r, &mut v);
        r
    }

    fn next_var_name(&mut self) -> String {
        let mut s = self.id.to_string();
        self.id += 1;
        s.insert(0, '?');
        s.insert(1, 'R');
        s
    }
}

struct RenamingVisitor<'a> {
    renamer: &'a mut VarRenamer,
    mapping: HashMap<Constant, Constant>
}

impl<'a> RenamingVisitor<'a> {
    fn new(renamer: &'a mut VarRenamer) -> RenamingVisitor {
        RenamingVisitor { renamer: renamer, mapping: HashMap::new() }
    }
}
use std::collections::hash_map::Entry::{Occupied, Vacant};
impl<'a> Visitor for RenamingVisitor<'a> {
    fn visit_variable(&mut self, var: &mut Variable) {
        let entry = self.mapping.entry(var.name.clone());
        var.name = match entry {
            Occupied(e) => (*e.get()).clone(),
            Vacant(e) => (*e.insert(Constant::new(self.renamer.next_var_name()))).clone()
        };
    }
}

pub struct Prover {
    knowledge_base: HashMap<Sentence, Vec<Rule>>
}

impl Prover {
    pub fn new(desc: Description) -> Prover {
        let mut knowledge_base = HashMap::new();
        for clause in desc.clauses {
            let (entry, r) = match clause {
                RuleClause(r) => (knowledge_base.entry(r.head.clone()), r),
                SentenceClause(s) => (knowledge_base.entry(s.clone()), s.into())
            };
            // The closure should prevent unnecessary allocation of empty `Vec`s
            let v = entry.or_insert_with(|| Vec::new());
            v.push(r);
        }
        Prover { knowledge_base: knowledge_base }
    }

    pub fn ask(&self, query: Sentence, state: &State) -> QueryResult {
        let mut goals = VecDeque::new();
        let query: Literal = query.into();
        goals.push_front(query.clone());

        let mut results = Vec::new();
        self.ask_goals(&mut goals, &mut results, &mut VarRenamer::new(), &mut Substitution::new(),
                       state);

        let mut props = HashSet::new();
        for theta in results {
            let s = match theta.substitute(&query) {
                PropLit(prop) => PropSentence(prop),
                RelLit(rel) => RelSentence(rel),
                _ => panic!("Expected sentence")
            };
            props.insert(s);
        }
        QueryResult { props: props }
    }

    fn ask_goals(&self, goals: &mut VecDeque<Literal>, results: &mut Vec<Substitution>,
                 renamer: &mut VarRenamer, theta: &mut Substitution, state: &State) {
        let l = match goals.pop_front() {
            None => { results.push(theta.clone()); return },
            Some(l) => l
        };

        let q = theta.substitute(&l);
        match q {
            OrLit(or) => self.ask_or(or, goals, results, renamer, theta, state),
            NotLit(not) => self.ask_not(not, goals, results, renamer, theta, state),
            DistinctLit(distinct) => self.ask_distinct(distinct, goals, results, renamer, theta,
                                                       state),
            PropLit(prop) => self.ask_prop(prop, goals, results, renamer, theta, state),
            RelLit(rel) => self.ask_rel(rel, goals, results, renamer, theta, state)
        }

        goals.push_front(l);
    }

    fn ask_prop(&self, prop: Proposition, goals: &mut VecDeque<Literal>,
                results: &mut Vec<Substitution>, renamer: &mut VarRenamer,
                theta: &mut Substitution, state: &State) {
        self.ask_rel(Relation::new(prop.name, Vec::new()), goals, results, renamer, theta, state);
    }

    fn ask_rel(&self, rel: Relation, goals: &mut VecDeque<Literal>,
               results: &mut Vec<Substitution>, renamer: &mut VarRenamer,
               theta: &mut Substitution, state: &State) {
        let mut candidates: HashSet<Rule> = HashSet::new();

        // Check whether the relation is already a true statement
        let rel_sentence = rel.clone().into();
        if state.props.contains(&rel_sentence) {
            candidates.insert(rel_sentence.into());
        }

        // Get all corresponding rules from the game description
        if let Some(rules) = self.knowledge_base.get(&rel.clone().into()) {
            for rule in rules.iter().cloned() {
                candidates.insert(rule);
            }
        }

        for rule in candidates {
            let rule = renamer.rename(&rule);
            let rel_head = match rule.head.clone() {
                PropSentence(p) => p.into(),
                RelSentence(r) => r
            };

            if let Some(theta_prime) = unify(rel_head, rel.clone()) {
                let mut new_goals = VecDeque::new();
                for r in rule.body.clone() {
                    new_goals.push_back(r);
                }
                new_goals.append(&mut goals.clone());
                self.ask_goals(&mut new_goals, results, renamer, &mut theta.compose(theta_prime),
                               state);
            }
        }
    }

    fn ask_or(&self, or: Or, goals: &mut VecDeque<Literal>, results: &mut Vec<Substitution>,
              renamer: &mut VarRenamer, theta: &mut Substitution, state: &State) {
        for lit in or.lits.into_iter() {
            goals.push_front(lit);
            self.ask_goals(goals, results, renamer, theta, state);
            goals.pop_front().unwrap();
        }
    }

    fn ask_not(&self, not: Not, goals: &mut VecDeque<Literal>, results: &mut Vec<Substitution>,
               renamer: &mut VarRenamer, theta: &mut Substitution, state: &State) {
        let mut not_goals = VecDeque::new();
        let mut not_results = Vec::new();

        not_goals.push_front(*not.lit);
        self.ask_goals(&mut not_goals, &mut not_results, renamer, theta, state);

        if not_results.is_empty() {
            self.ask_goals(goals, results, renamer, theta, state);
        }
    }

    fn ask_distinct(&self, distinct: Distinct, goals: &mut VecDeque<Literal>,
                    results: &mut Vec<Substitution>, renamer: &mut VarRenamer,
                    theta: &mut Substitution, state: &State) {
        if distinct.term1 != distinct.term2 {
            self.ask_goals(goals, results, renamer, theta, state);
        }
    }

    pub fn prove(&self, s: Sentence, state: &State) -> bool {
        !self.ask(s, state).props.is_empty()
    }
}

fn unify(r1: Relation, r2: Relation) -> Option<Substitution> {
    let x = Function::new(r1.name, r1.args).into();
    let y = Function::new(r2.name, r2.args).into();
    unify_term(x, y, Substitution::new())
}

fn unify_term(x: Term, y: Term, theta: Substitution) -> Option<Substitution> {
    if x == y {
        return Some(theta)
    }

    match (x.clone(), y.clone()) {
        (VarTerm(v), _) => unify_variable(v, y, theta),
        (_, VarTerm(v)) => unify_variable(v, x, theta),
        (ConstTerm(_), ConstTerm(_)) => None,
        (FuncTerm(f1), FuncTerm(f2)) => {
            match unify_term(f1.name.into(), f2.name.into(), theta) {
                Some(theta) => {
                    assert_eq!(f1.args.len(), f2.args.len());
                    let mut theta = theta;
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
    if let Some(t) = theta.get(&x).cloned() {
        return unify_term(t, y, theta);
    }
    if let VarTerm(v) = y.clone() {
        if let Some(t) = theta.get(&v).cloned() {
            return unify_term(x.into(), t, theta)
        }
    }

    // Neither x nor y were found in theta
    theta.insert(x, y);
    Some(theta)
}

pub struct QueryResult {
    props: HashSet<Sentence>
}

impl QueryResult {
    pub fn into_state(self) -> State {
        State { props: self.props }
    }

    pub fn into_moves(self) -> Vec<Move> {
        let mut moves = Vec::new();
        for s in self.props {
            let term = match s {
                PropSentence(p) => p.name.into(),
                RelSentence(r) => Function::new(r.name, r.args).into()
            };
            moves.push(Move::new(term));
        }
        moves
    }

    pub fn into_score(self) -> Score {
        assert_eq!(self.props.len(), 1);
        match self.props.into_iter().next().unwrap() {
            RelSentence(mut r) => {
                assert_eq!(r.name, Constant::new("goal"));
                assert_eq!(r.args.len(), 1);
                let score = r.args.swap_remove(0);
                match score {
                    ConstTerm(c) => c.name.parse().unwrap(),
                    _ => panic!("Expected ConstTerm")
                }
            },
            _ => panic!("Expected RelSentence")
        }
    }
}

pub mod query_builder {
    use gdl::{Sentence, Relation, Proposition, Constant, Variable, Term, Role};
    use gdl::Sentence::{RelSentence, PropSentence};
    use gdl::Term::{VarTerm, ConstTerm};

    pub fn next_query() -> Sentence {
        RelSentence(Relation::new(create_const("next"), vec![create_var_term("x")]))
    }

    pub fn terminal_query() -> Sentence {
        PropSentence(Proposition::new(create_const("terminal")))
    }

    pub fn legal_query(role: &Role) -> Sentence {
        RelSentence(Relation::new(create_const("legal"), vec![ConstTerm(create_const(role.name())),
                                                              create_var_term("m")]))
    }

    pub fn goal_query(role: &Role) -> Sentence {
        RelSentence(Relation::new(create_const("goal"), vec![ConstTerm(create_const(role.name())),
                                                             create_var_term("s")]))
    }

    pub fn init_query() -> Sentence {
        RelSentence(Relation::new(create_const("init"), vec![create_var_term("i")]))
    }

    fn create_var_term(name: &str) -> Term {
        VarTerm(Variable::new(create_const(name)))
    }

    fn create_const(name: &str) -> Constant {
        Constant::new(name.to_string())
    }
}
