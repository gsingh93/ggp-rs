use std::collections::{HashSet, HashMap, VecDeque};

use game_manager::State;
use gdl::{Description, Sentence, Proposition, Relation, Move, Score, Literal, Or, Not, Distinct,
          Variable, Constant};
use gdl::Literal::{OrLit, NotLit, DistinctLit, PropLit, RelLit};
use gdl::Sentence::{PropSentence, RelSentence};

use visitor::Visitor;

pub struct Prover {
    desc: Description
}

#[derive(Clone)]
struct Substitution {
    mapping: HashMap<Variable, Constant>
}

struct SubstitutionVisitor;

impl Visitor for SubstitutionVisitor {

}

impl Substitution {
    fn new() -> Substitution {
        Substitution { mapping: HashMap::new() }
    }
    fn substitute(&self, l: &Literal) -> Literal {
        panic!("unimplemented")
    }

    fn compose(theta: Substitution) -> Substitution {
        panic!("unimplemented")
    }
}

struct VarRenamer {
    id: u32
}

impl VarRenamer {
    fn new() -> VarRenamer {
        VarRenamer { id: 0 }
    }

    fn next_var_name(&mut self) -> String {
        let mut s = self.id.to_string();
        self.id += 1;
        s.insert(0, '?');
        s.insert(1, 'R');
        s
    }
}

impl Prover {
    pub fn new(desc: Description) -> Prover {
        Prover { desc: desc }
    }

    pub fn ask(&self, query: Sentence, state: &State) -> QueryResult {
        let mut goals = VecDeque::new();
        let query: Literal = query.into();
        goals.push_front(query.clone());

        let mut results = Vec::new();
        self.ask_goals(&mut goals, &mut results, &mut Substitution::new());

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
                theta: &mut Substitution) {
        let l = match goals.pop_front() {
            None => { results.push(theta.clone()); return },
            Some(l) => l
        };

        let q = theta.substitute(&l);
        match q {
            OrLit(or) => self.ask_or(or, goals, results, theta),
            NotLit(not) => self.ask_not(not, goals, results, theta),
            DistinctLit(distinct) => self.ask_distinct(distinct, goals, results, theta),
            PropLit(prop) => self.ask_prop(prop, goals, results, theta),
            RelLit(rel) => self.ask_rel(rel, goals, results, theta)
        }

        goals.push_front(l);
    }

    fn ask_prop(&self, prop: Proposition, goals: &mut VecDeque<Literal>,
               results: &mut Vec<Substitution>, theta: &mut Substitution) {
        self.ask_rel(Relation::new(prop.name, Vec::new()), goals, results, theta);
    }

    fn ask_rel(&self, rel: Relation, goals: &mut VecDeque<Literal>,
              results: &mut Vec<Substitution>, theta: &mut Substitution) {

    }

    fn ask_or(&self, or: Or, goals: &mut VecDeque<Literal>, results: &mut Vec<Substitution>,
             theta: &mut Substitution) {
        for lit in or.lits.into_iter() {
            goals.push_front(lit);
            self.ask_goals(goals, results, theta);
            goals.pop_front().unwrap();
        }
    }

    fn ask_not(&self, not: Not, goals: &mut VecDeque<Literal>, results: &mut Vec<Substitution>,
              theta: &mut Substitution) {
        let mut not_goals = VecDeque::new();
        let mut not_results = Vec::new();

        not_goals.push_front(*not.lit);
        self.ask_goals(&mut not_goals, &mut not_results, theta);

        if not_results.is_empty() {
            self.ask_goals(goals, results, theta);
        }
    }

    fn ask_distinct(&self, distinct: Distinct, goals: &mut VecDeque<Literal>,
                   results: &mut Vec<Substitution>, theta: &mut Substitution) {
        if distinct.term1 != distinct.term2 {
            self.ask_goals(goals, results, theta);
        }
    }

    pub fn prove(&self, s: Sentence, state: &State) -> bool {
        !self.ask(s, state).props.is_empty()
    }
}

pub struct QueryResult {
    props: HashSet<Sentence>
}

impl QueryResult {
    pub fn into_state(self) -> State {
        panic!("unimplemented")
    }

    pub fn into_moves(self) -> Vec<Move> {
        panic!("unimplemented")
    }

    pub fn into_score(self) -> Score {
        panic!("unimplemented")
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
