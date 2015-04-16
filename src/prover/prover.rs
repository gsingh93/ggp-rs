use std::collections::{HashSet, HashMap, VecDeque};
use std::collections::hash_map::Entry::{Occupied, Vacant};

use game_manager::State;
use prover::negative_literal_mover;

use gdl::{Description, Sentence, Proposition, Relation, Move, Score, Literal, Or, Not, Distinct,
          Variable, Constant, Term, Function, Rule};
use gdl::Clause::{SentenceClause, RuleClause};
use gdl::Literal::{OrLit, NotLit, DistinctLit, PropLit, RelLit};
use gdl::Sentence::{PropSentence, RelSentence};
use gdl::Term::{VarTerm, ConstTerm, FuncTerm};

use gdl_parser::visitor::{self, Visitor};

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

#[derive(Clone, Debug, Eq, PartialEq)]
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

impl<'a> Visitor for RenamingVisitor<'a> {
    fn visit_variable(&mut self, var: &mut Variable) {
        let entry = self.mapping.entry(var.name.clone());
        var.name = match entry {
            Occupied(e) => (*e.get()).clone(),
            Vacant(e) => (*e.insert(Constant::new(self.renamer.next_var_name()))).clone()
        };
    }
}

type RuleMap = HashMap<Constant, Vec<Rule>>;

pub struct Prover {
    rule_map: RuleMap
}

impl Prover {
    pub fn new(desc: Description) -> Prover {
        let desc = negative_literal_mover::run(desc);

        let mut rule_map = HashMap::new();
        for clause in desc.clauses {
            let (entry, r) = match clause {
                RuleClause(r) => (rule_map.entry(r.head.name().clone()), r),
                SentenceClause(s) => (rule_map.entry(s.name().clone()), s.into())
            };
            // The closure should prevent unnecessary allocation of empty `Vec`s
            let v = entry.or_insert_with(|| Vec::new());
            v.push(r);
        }
        Prover { rule_map: rule_map }
    }

    pub fn ask(&self, query: Sentence, state: State) -> QueryResult {
        let mut goals = VecDeque::new();
        let query: Literal = query.into();
        goals.push_front(query.clone());

        let mut trues = Vec::new();
        let mut does = Vec::new();
        let true_const = Constant::new("true");
        let does_const = Constant::new("does");
        for s in state.props {
            if *s.name() == true_const {
                trues.push(s.into())
            } else if *s.name() == does_const {
                does.push(s.into());
            }
        }
        let mut context = RuleMap::new();
        context.insert(Constant::new("true"), trues);
        context.insert(Constant::new("does"), does);
        debug!("context: {:?}", context);

        let mut results = Vec::new();
        self.ask_goals(&mut goals, &mut results, &mut VarRenamer::new(), &mut Substitution::new(),
                       &context);

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
                 renamer: &mut VarRenamer, theta: &mut Substitution, state: &RuleMap) {
        debug!("goals: {:?}", goals);
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
                theta: &mut Substitution, state: &RuleMap) {
        self.ask_rel(Relation::new(prop.name, Vec::new()), goals, results, renamer, theta, state);
    }

    fn ask_rel(&self, rel: Relation, goals: &mut VecDeque<Literal>,
               results: &mut Vec<Substitution>, renamer: &mut VarRenamer,
               theta: &mut Substitution, state: &RuleMap) {
        let mut candidates: HashSet<Rule> = HashSet::new();

        // Check whether the relation is already a true statement
        if let Some(rules) = state.get(&rel.name) {
            for rule in rules.iter().cloned() {
                candidates.insert(rule);
            }
        }

        // Get all corresponding rules from the game description
        if let Some(rules) = self.rule_map.get(&rel.name) {
            for rule in rules.iter().cloned() {
                candidates.insert(rule);
            }
        }

        debug!("{} candidates found for unification", candidates.len());
        for rule in candidates {
            let rule = renamer.rename(&rule);
            let rel_head = match rule.head.clone() {
                PropSentence(p) => p.into(),
                RelSentence(r) => r
            };

            debug!("Unifying {:?} and {:?}", rel_head, rel);
            if let Some(theta_prime) = unify(rel_head, rel.clone()) {
                debug!("Unification Success");
                let mut new_goals = VecDeque::new();
                for r in rule.body.clone() {
                    new_goals.push_back(r);
                }
                new_goals.append(&mut goals.clone());
                self.ask_goals(&mut new_goals, results, renamer, &mut theta.compose(theta_prime),
                               state);
            } else {
                debug!("Unification failure");
            }
        }
    }

    fn ask_or(&self, or: Or, goals: &mut VecDeque<Literal>, results: &mut Vec<Substitution>,
              renamer: &mut VarRenamer, theta: &mut Substitution, state: &RuleMap) {
        for lit in or.lits.into_iter() {
            goals.push_front(lit);
            self.ask_goals(goals, results, renamer, theta, state);
            goals.pop_front().unwrap();
        }
    }

    fn ask_not(&self, not: Not, goals: &mut VecDeque<Literal>, results: &mut Vec<Substitution>,
               renamer: &mut VarRenamer, theta: &mut Substitution, state: &RuleMap) {
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
                    theta: &mut Substitution, state: &RuleMap) {
        if distinct.term1 != distinct.term2 {
            self.ask_goals(goals, results, renamer, theta, state);
        }
    }

    pub fn prove(&self, s: Sentence, state: State) -> bool {
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
            match unify_term(f1.name.clone().into(), f2.name.clone().into(), theta) {
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
        let mut trues = HashSet::new();
        for s in self.props {
            match s {
                RelSentence(mut r) => {
                    assert_eq!(r.args.len(), 1);
                    trues.insert(Relation::new("true", vec![r.args.swap_remove(0)]).into());
                },
                _ => panic!("Expected RelSentence")
            }
        }
        State { props: trues }
    }

    pub fn into_moves(self) -> Vec<Move> {
        let mut moves = Vec::new();
        for s in self.props {
            let term = match s {
                RelSentence(mut r) => r.args.swap_remove(1),
                _ => panic!("Expected RelSentence")
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
                assert_eq!(r.args.len(), 2);
                let score = r.args.swap_remove(1);
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
    use gdl::{Sentence, Relation, Proposition, Constant, Variable, Role};

    pub fn next_query() -> Sentence {
        Relation::new("next", vec![Variable::new("x").into()]).into()
    }

    pub fn terminal_query() -> Sentence {
        Proposition::new("terminal").into()
    }

    pub fn legal_query(role: &Role) -> Sentence {
        Relation::new("legal", vec![Constant::new(role.name()).into(),
                                    Variable::new("m").into()]).into()
    }

    pub fn goal_query(role: &Role) -> Sentence {
        Relation::new("goal", vec![Constant::new(role.name()).into(),
                                               Variable::new("s").into()]).into()
    }

    pub fn init_query() -> Sentence {
        Relation::new("init", vec![Variable::new("i").into()]).into()
    }
}

#[cfg(test)]
mod test {
    use std::collections::{HashMap, HashSet};

    use gdl::{self, Relation, Description, Constant, Function, Variable, Role, Move};
    use gdl::Sentence::RelSentence;
    use gdl::Clause::SentenceClause;

    use game_manager::State;

    use super::{unify, query_builder, Prover, Substitution};

    fn to_relation(mut desc: Description) -> Relation {
        let c = desc.clauses.swap_remove(0);
        match c {
            SentenceClause(s) => match s {
                RelSentence(r) => r,
                _ => panic!("")
            },
            _ => panic!("")
        }
    }

    #[test]
    fn test_unify() {
        let a = to_relation(gdl::parse("(legal white ?l)"));
        let b = to_relation(gdl::parse("(legal ?p (reduce ?x ?n))"));
        let c = to_relation(gdl::parse("(reduce ?x ?n)"));

        let mut map = HashMap::new();
        map.insert(Variable::new("p"), Constant::new("white").into());
        map.insert(Variable::new("l"), Function::new(c.name, c.args).into());
        let theta = Substitution { mapping: map };
        assert_eq!(unify(a, b).unwrap(), theta);
    }

    #[test]
    fn test_substitute() {
        let a = to_relation(gdl::parse("(legal ?p ?m)")).into();
        let b = to_relation(gdl::parse("(legal white (reduce a 1))")).into();

        let mut mapping = HashMap::new();
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

    #[test]
    fn test_ask() {
        let nim = "
        (<= (legal ?p (reduce ?x ?n)) (true (control ?p)) (true (heap ?x ?m)) (smaller ?n ?m))

        (<= (smaller ?x ?y) (succ ?x ?y))
        (<= (smaller ?x ?y) (succ ?x ?z) (smaller ?z ?y))
        (succ 0 1)
        (succ 1 2)
        (succ 2 3)
        (succ 3 4)
        (succ 4 5)

        (init (heap a 2))
        (init (heap b 0))
        (init (heap c 5))
        (init (control white))";

        let prover = Prover::new(gdl::parse(nim));
        let init_state = prover.ask(query_builder::init_query(), State::new()).into_state();
        let mut expected_moves = HashSet::new();
        for i in 0..2 {
           expected_moves.insert(Move::new(
               Function::new("reduce", vec![Constant::new("a").into(),
                                            Constant::new(i.to_string()).into()]).into()));
        }
        for i in 0..5 {
            expected_moves.insert(Move::new(Function::new("reduce",
                                                          vec![Constant::new("c").into(),
                                                               Constant::new(i.to_string()).into()]).into()));
        }

        let results = prover.ask(query_builder::legal_query(&Role::new("white")),
                                 init_state).into_moves();
        let results_len = results.len();
        let results_set: HashSet<Move> = results.into_iter().collect();
        assert_eq!(results_set.len(), results_len);
        assert_eq!(results_set, expected_moves);
    }

    #[test]
    fn test_next_state() {
        let gdl = "(role black) (role red) \
                   (<= (legal black noop) (true (control red))) \
                   (<= (legal red noop) (true (control black))) \
                   (<= (legal black p) (true (control black))) \
                   (<= (legal red p) (true (control red))) \
                   (init (control black)) \
                   (<= (next (control black)) (true (control red))) \
                   (<= (next (control red)) (true (control black)))";
        let prover = Prover::new(gdl::parse(gdl));
        let init_state = prover.ask(query_builder::init_query(), State::new()).into_state();
        let mut props = HashSet::new();
        props.insert(
            Relation::new("true",
                          vec![Function::new("control",
                                             vec![Constant::new("black").into()]).into()]).into());
        assert_eq!(init_state, State { props: props });
        let next_state = prover.ask(query_builder::next_query(), init_state).into_state();

        let mut props = HashSet::new();
        props.insert(
            Relation::new("true",
                          vec![Function::new("control",
                                             vec![Constant::new("red").into()]).into()]).into());
        assert_eq!(next_state, State { props: props })
    }

    #[test]
    fn test_next_state_does() {
        let gdl = "(role black) (role red) \
                   (<= (legal black noop) (true (control red))) \
                   (<= (legal red noop) (true (control black))) \
                   (<= (legal black p) (true (control black))) \
                   (<= (legal red p) (true (control red))) \
                   (init (control black)) \
                   (<= (next (control black)) (true (control red))) \
                   (<= (next (control red)) (true (control black))) \
                   (<= (next q) (or (does red p) (true q))) \
                   (<= (next s) (or (does black p) (true s)))";
        let prover = Prover::new(gdl::parse(gdl));
        let mut init_state = prover.ask(query_builder::init_query(), State::new()).into_state();
        let mut props = HashSet::new();
        props.insert(Relation::new(
            "true",
            vec![Function::new("control",
                               vec![Constant::new("black").into()]).into()]).into());
        assert_eq!(init_state, State { props: props });

        init_state.props.insert(
            Relation::new("does",
                          vec![Constant::new("red").into(), Constant::new("p").into()]).into());
        init_state.props.insert(
            Relation::new("does",
                          vec![Constant::new("black").into(), Constant::new("p").into()]).into());

        let next_state = prover.ask(query_builder::next_query(), init_state).into_state();

        let mut props = HashSet::new();
        props.insert(
            Relation::new("true",
                          vec![Function::new(Constant::new("control"),
                                             vec![Constant::new("red").into()]).into()]).into());
        props.insert(Relation::new("true", vec![Constant::new("q").into()]).into());
        props.insert(Relation::new("true", vec![Constant::new("s").into()]).into());
        assert_eq!(next_state, State { props: props })
    }
}
