//! Contains objects for proving queries about a game description. A description of the algorithms
//! used can be found [here](http://logic.stanford.edu/ggp/chapters/chapter_13.html).
//!
//! One addition in this code is the recursion checking. We check if we are asking about a relation
//! we have previously asked about but have not received an answer for. In this case, we mark that
//! this has happened for this relation, return, and continue proving other subgoals. Once the
//! remaining subgoals have been proved, we return to the marked relation and attempt to prove it
//! until no new substitutions are found.
//!
//! Another addition is the caching. We cache queries we have answered before during the execution
//! of the algorithm in one cache, and we also cache queries that will never change during the
//! lifetime of the game in another cache.

use std::collections::{HashSet, HashMap, VecDeque, BTreeSet};
use std::cell::RefCell;
use std::sync::Arc;

use game_manager::State;
use prover::negative_literal_mover;
use prover::unification::unify;
use prover::substitution::Substitution;
use prover::renamer::VarRenamer;
use util::literal_into_relation;

use gdl::{constants, Description, Sentence, Proposition, Relation, Move, Score, Literal, Or,
          Not, Distinct, Constant, Rule};
use gdl::Clause::{SentenceClause, RuleClause};
use gdl::Literal::{OrLit, NotLit, DistinctLit, PropLit, RelLit};
use gdl::Sentence::{PropSentence, RelSentence};
use gdl::Term::ConstTerm;

struct Cache {
    cache: HashMap<Arc<Relation>, HashSet<Relation>>
}

impl Cache {
    fn new() -> Cache {
        Cache { cache: HashMap::new() }
    }

    fn insert(&mut self, rel: &Relation, renamed_rel: Arc<Relation>,
              results: &HashSet<Substitution>) {
        // We store relations instead of substitutions so that if the same sentence is queried
        // with different variables, we can extract a new substitution that uses the correct
        // variables.
        let mut sentences = HashSet::with_capacity(results.len());
        for res in results.iter() {
            sentences.insert(literal_into_relation(res.substitute(&rel.clone().into())));
        }
        self.cache.insert(renamed_rel, sentences);
    }

    fn get(&self, rel: &Relation, renamed_rel: &Relation) -> Option<HashSet<Substitution>> {
        match self.cache.get(renamed_rel) {
            Some(sentences) => {
                let mut results = HashSet::with_capacity(sentences.len());
                for sentence in sentences.iter().cloned() {
                    results.insert(unify(sentence, rel.clone()).unwrap());
                }
                Some(results)
            }
            None => None
        }
    }
}

struct RecursionContext {
    /// Contains all relations that have been asked about but have not received answers
    already_asking: HashSet<Arc<Relation>>,

    /// Contains all relations that have asked about themselves recursively
    called_recursively: HashSet<Arc<Relation>>,

    /// Contains a mapping of relations to their (possibly partial) unification results
    previous_results: HashMap<Arc<Relation>, HashSet<Relation>>,
    state: RuleMap,
    renamer: VarRenamer,

    /// This caches results for relations we've seen during the proving of the original query
    cache: Cache,
}

impl RecursionContext {
    fn new(state: RuleMap) -> RecursionContext {
        RecursionContext { already_asking: HashSet::new(), called_recursively: HashSet::new(),
                           previous_results: HashMap::new(), state: state,
                           renamer: VarRenamer::new(), cache: Cache::new() }
    }
}

/// A mapping between rule heads and rules
struct RuleMap {
    map: HashMap<Constant, Vec<Arc<Rule>>>
}

impl RuleMap {
    fn from_description(desc: Description) -> RuleMap {
        let mut rule_map = HashMap::with_capacity(desc.clauses.len());
        for clause in desc.clauses {
            let (entry, r) = match clause {
                RuleClause(r) => (rule_map.entry(r.head.name().clone()), r),
                SentenceClause(s) => (rule_map.entry(s.name().clone()), s.into())
            };
            // The closure should prevent unnecessary allocation of empty `Vec`s
            let v = entry.or_insert_with(|| Vec::new());
            v.push(Arc::new(r));
        }
        RuleMap { map: rule_map }
    }

    fn from_state(state: &State) -> RuleMap {
        let mut trues = Vec::new();
        let mut does = Vec::new();
        for s in state.props().iter().cloned() {
            if *s.name() == *constants::TRUE_CONST {
                trues.push(Arc::new(s.into()))
            } else if *s.name() == *constants::DOES_CONST {
                does.push(Arc::new(s.into()));
            } else {
                panic!("State contains something other than `true` and `does`");
            }
        }
        if cfg!(not(ndebug)) {
            let state_str: Vec<_> =
                trues.iter().chain(does.iter()).map(|x: &Arc<Rule>| x.head.to_string()).collect();
            debug!("state: {:?}", state_str);
        }
        let mut rule_map = HashMap::new();
        rule_map.insert(Constant::new("true"), trues);
        rule_map.insert(Constant::new("does"), does);

        RuleMap { map: rule_map }
    }

    fn get(&self, name: &Constant) -> Option<&Vec<Arc<Rule>>> {
        self.map.get(name)
    }
}

pub struct Prover {
    rule_map: RuleMap,

    /// This caches results for relations whose results will never change
    fixed_cache: RefCell<Cache>
}

impl Prover {
    pub fn new(desc: Description) -> Prover {
        let desc = negative_literal_mover::reorder(desc);
        Prover { rule_map: RuleMap::from_description(desc),
                 fixed_cache: RefCell::new(Cache::new()) }
    }

    /// Ask whether the query `query` is true in the state `state`
    pub fn prove(&self, query: Sentence, state: &State) -> bool {
        !self.ask(query, state).props.is_empty()
    }

    /// Ask whether the query `query` is true in the state `state`
    pub fn ask(&self, query: Sentence, state: &State) -> QueryResult {
        let mut goals = VecDeque::new();
        let query: Literal = query.into();
        goals.push_front(query.clone());

        let mut context = RecursionContext::new(RuleMap::from_state(state));
        let mut results = HashSet::new();
        self.ask_goals(&mut goals, &mut results, &mut Substitution::new(), &mut context);

        let mut props = HashSet::with_capacity(results.len());
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

    fn ask_goals(&self, goals: &mut VecDeque<Literal>, results: &mut HashSet<Substitution>,
                 theta: &mut Substitution, context: &mut RecursionContext) -> bool {
        if cfg!(debug_assertions) {
            let goal_str: Vec<String> = goals.iter().map(|x| x.to_string()).collect();
            debug!("goals: {:?}", goal_str);
        }

        let l = match goals.pop_front() {
            // TODO: Why true?
            None => { results.insert(theta.clone()); return true; },
            Some(l) => l
        };

        let q = theta.substitute(&l);
        debug!("Goal query: {} (original: {})", q, l);
        let is_constant = match q {
            OrLit(or) => self.ask_or(or, goals, results, theta, context),
            NotLit(not) => self.ask_not(not, goals, results, theta, context),
            DistinctLit(distinct) => self.ask_distinct(distinct, goals, results, theta, context),
            PropLit(prop) => self.ask_prop(prop, goals, results, theta, context),
            RelLit(rel) => self.ask_rel(rel, goals, results, theta, context)
        };

        goals.push_front(l);

        is_constant
    }

    fn ask_prop(&self, prop: Proposition, goals: &mut VecDeque<Literal>,
                results: &mut HashSet<Substitution>, theta: &mut Substitution,
                context: &mut RecursionContext) -> bool {
        self.ask_rel(prop.into(), goals, results, theta, context)
    }

    fn ask_rel(&self, rel: Relation, goals: &mut VecDeque<Literal>,
               results: &mut HashSet<Substitution>, theta: &mut Substitution,
               context: &mut RecursionContext) -> bool {
        // We use the renamed relation as the key for any hash tables, as this can be used as a
        // canonical (i.e. unchanging) representation of the query
        let renamed_rel = match VarRenamer::new().rename_sentence(&rel.clone().into()) {
            RelSentence(rel) => rel,
            _ => panic!("Expected relation")
        };
        let renamed_rel = Arc::new(renamed_rel);

        // If the answer to this query exists in the fixed cache, return it. Otherwise, check the
        // normal cache.
        let cache_res = if let Some(sentences) = self.fixed_cache.borrow().get(&rel,
                                                                               &renamed_rel) {
            (Some(sentences), true)
        } else {
            // True or does relations can never be constant, as they depend on the moves the player
            // makes and the state of the game
            let true_or_does = rel.name == *constants::DOES_CONST
                || rel.name == *constants::TRUE_CONST;
            if let Some(sentences) = context.cache.get(&rel, &renamed_rel) {
                (Some(sentences), !true_or_does)
            } else {
                (None, !true_or_does)
            }
        };
        let (cached_sentences, mut is_constant) = cache_res;

        // If the answer to our query wasn't cached, we need to find the answer
        let sentences = if cached_sentences.is_none() {

            // If we've already asked about this query but haven't gotten an answer, mark that
            // this query was called recursively and return any results obtained from the last time
            // this happened.
            if context.already_asking.contains(&renamed_rel) {
                debug!("Recursively called {}, backtracking", renamed_rel);
                context.called_recursively.insert(renamed_rel.clone());
                let prev_results = context.previous_results.entry(renamed_rel)
                    .or_insert_with(|| HashSet::new()).clone();
                for res in prev_results {
                    let theta_prime = unify(res, rel.clone()).unwrap();
                    is_constant = is_constant &
                        self.ask_goals(goals, results, &mut theta.compose(theta_prime), context);
                }
                return is_constant;
            }
            context.already_asking.insert(renamed_rel.clone());

            let mut candidates: HashSet<Arc<Rule>> = HashSet::new();

            // Check whether the relation is already a true statement
            if let Some(rules) = context.state.get(&rel.name) {
                candidates.extend(rules.clone());
            }

            // Get all corresponding rules from the game description
            if let Some(rules) = self.rule_map.get(&rel.name) {
                candidates.extend(rules.clone());
            }

            let mut new_results = self.get_relation_results(&rel, theta, &candidates,
                                                            context, &mut is_constant);
            debug!("{} results from unifying {}", new_results.len(), rel);

            // If the query we just asked about was called recursively at some point, we returned
            // early and did not get all the results. We continuously ask about this query until
            // we get know new results, at which point we should have all the results.
            if context.called_recursively.contains(&renamed_rel) {
                debug!("Rehandling {} due to recursive call", renamed_rel);
                let mut sentence_results = HashSet::with_capacity(new_results.len());
                for res in new_results.iter() {
                    let s: Sentence = rel.clone().into();
                    let l: Literal = s.into();
                    let sentence = literal_into_relation(res.substitute(&l));
                    sentence_results.insert(sentence);
                }

                while sentence_results.len() >
                    context.previous_results.get_mut(&renamed_rel).unwrap().len() {

                    assert!(context.called_recursively.remove(&renamed_rel));
                    context.previous_results.get_mut(&renamed_rel).unwrap()
                        .extend(sentence_results);

                    new_results = self.get_relation_results(&rel, theta, &candidates,
                                                            context, &mut is_constant);

                    sentence_results = HashSet::with_capacity(new_results.len());
                    for res in new_results.iter() {
                        let s: Sentence = rel.clone().into();
                        let l: Literal = s.into();
                        let sentence = literal_into_relation(res.substitute(&l));
                        sentence_results.insert(sentence);
                    }
                }
                assert!(context.called_recursively.remove(&renamed_rel));
                assert!(context.previous_results.remove(&renamed_rel).is_some());
            }
            assert!(context.already_asking.remove(&renamed_rel));
            // We only insert into the cache if no query has been asked about recursively,
            // otherwise we may insert partial results into the cache
            if context.called_recursively.is_empty() {
                if is_constant {
                    self.fixed_cache.borrow_mut().insert(&rel, renamed_rel.clone(), &new_results);
                } else {
                    context.cache.insert(&rel, renamed_rel.clone(), &new_results);
                }
            }
            new_results
        } else {
            cached_sentences.unwrap()
        };

        for res in sentences {
            is_constant = is_constant & self.ask_goals(goals, results, &mut theta.compose(res),
                                                       context);
        }
        is_constant
    }

    fn get_relation_results(&self, rel: &Relation, theta: &Substitution,
                            candidates: &HashSet<Arc<Rule>>, context: &mut RecursionContext,
                            is_constant: &mut bool) -> HashSet<Substitution> {
        let mut new_results = HashSet::new();
        debug!("{} candidates found for unification", candidates.len());
        if cfg!(debug_assertions) {
            let candidate_str: Vec<_> = candidates.iter().map(|x| x.to_string()).collect();
            debug!("Possible candidates: {:?}", candidate_str);
        }
        for rule in candidates.iter() {
            let rule = context.renamer.rename_rule(rule);
            let rel_head = match rule.head {
                PropSentence(p) => p.into(),
                RelSentence(r) => r
            };

            // If the unification of the query and the head of a rule is successful, attempt to
            // prove the body of the rule.
            debug!("Unifying {} and {}", rel_head, rel);
            if let Some(theta_prime) = unify(rel_head, (*rel).clone()) {
                debug!("Unification Success");
                let mut new_goals = VecDeque::new();
                new_goals.extend(rule.body);
                *is_constant = *is_constant &
                    self.ask_goals(&mut new_goals, &mut new_results,
                                   &mut theta.compose(theta_prime), context);
                debug!("Continuing unification loop for {}", rel);
            } else {
                debug!("Unification failure");
            }
        }
        new_results
    }

    fn ask_or(&self, or: Or, goals: &mut VecDeque<Literal>, results: &mut HashSet<Substitution>,
              theta: &mut Substitution, context: &mut RecursionContext) -> bool {
        let mut is_constant = true;
        for lit in or.lits.into_iter() {
            goals.push_front(lit);
            is_constant = is_constant & self.ask_goals(goals, results, theta, context);
            goals.pop_front().unwrap();
        }
        is_constant
    }

    fn ask_not(&self, not: Not, goals: &mut VecDeque<Literal>, results: &mut HashSet<Substitution>,
               theta: &mut Substitution, context: &mut RecursionContext) -> bool {
        let mut not_goals = VecDeque::new();
        let mut not_results = HashSet::new();

        not_goals.push_front(*not.lit);
        let mut is_constant = self.ask_goals(&mut not_goals, &mut not_results, theta, context);

        if not_results.is_empty() {
            is_constant = is_constant & self.ask_goals(goals, results, theta, context);
        }
        is_constant
    }

    fn ask_distinct(&self, distinct: Distinct, goals: &mut VecDeque<Literal>,
                    results: &mut HashSet<Substitution>, theta: &mut Substitution,
                    context: &mut RecursionContext) -> bool {
        if distinct.term1 != distinct.term2 {
            self.ask_goals(goals, results, theta, context)
        } else {
            true
        }
    }
}

pub struct QueryResult {
    props: HashSet<Sentence>
}

impl QueryResult {
    pub fn into_state(self) -> State {
        let mut trues = BTreeSet::new();
        for s in self.props {
            match s {
                RelSentence(mut r) => {
                    assert_eq!(r.args.len(), 1);
                    trues.insert(Relation::new("true", vec![r.args.swap_remove(0)]).into());
                },
                _ => panic!("Expected RelSentence")
            }
        }
        State::from_props(trues)
    }

    pub fn into_moves(self) -> Vec<Move> {
        let mut moves = Vec::with_capacity(self.props.len());
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
        let goal_const = Constant::new("goal");
        match self.props.into_iter().next().unwrap() {
            RelSentence(mut r) => {
                assert_eq!(r.name, goal_const);
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
    use std::collections::{HashSet, BTreeSet};
    use std::fs::File;
    use std::io::Read;

    use gdl::{self, Relation, Constant, Function, Role, Move};
    use game_manager::State;
    use super::{query_builder, Prover};

    fn construct_prover(filename: &str) -> (Prover, State) {
        let mut gdl = String::new();
        File::open(filename).unwrap().read_to_string(&mut gdl).ok();

        let prover = Prover::new(gdl::parse(&gdl));
        let init_state = prover.ask(query_builder::init_query(), &State::new()).into_state();

        (prover, init_state)
    }

    #[test]
    fn test_ask() {
        let (prover, init_state) = construct_prover("resources/nim.gdl");

        let mut expected_moves = HashSet::new();
        for i in 0..2 {
           expected_moves.insert(Move::new(
               Function::new("reduce", vec![Constant::new("a").into(),
                                            Constant::new(i.to_string()).into()]).into()));
        }
        for i in 0..5 {
            expected_moves.insert(Move::new(
                Function::new("reduce",
                              vec![Constant::new("c").into(),
                                   Constant::new(i.to_string()).into()]).into()));
        }

        let results = prover.ask(query_builder::legal_query(&Role::new("white")),
                                 &init_state).into_moves();
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
        let init_state = prover.ask(query_builder::init_query(), &State::new()).into_state();
        let mut props = BTreeSet::new();
        props.insert(
            Relation::new("true",
                          vec![Function::new("control",
                                             vec![Constant::new("black").into()]).into()]).into());
        assert_eq!(init_state, State::from_props(props));
        let next_state = prover.ask(query_builder::next_query(), &init_state).into_state();

        let mut props = BTreeSet::new();
        props.insert(
            Relation::new("true",
                          vec![Function::new("control",
                                             vec![Constant::new("red").into()]).into()]).into());
        assert_eq!(next_state, State::from_props(props))
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
        let init_state = prover.ask(query_builder::init_query(), &State::new()).into_state();
        let mut props = BTreeSet::new();
        props.insert(Relation::new(
            "true",
            vec![Function::new("control",
                               vec![Constant::new("black").into()]).into()]).into());
        assert_eq!(init_state, State::from_props(props.clone()));

        props.insert(
            Relation::new("does",
                          vec![Constant::new("red").into(), Constant::new("p").into()]).into());
        props.insert(
            Relation::new("does",
                          vec![Constant::new("black").into(), Constant::new("p").into()]).into());

        let next_state = prover.ask(query_builder::next_query(),
                                    &State::from_props(props)).into_state();

        let mut props = BTreeSet::new();
        props.insert(
            Relation::new("true",
                          vec![Function::new(Constant::new("control"),
                                             vec![Constant::new("red").into()]).into()]).into());
        props.insert(Relation::new("true", vec![Constant::new("q").into()]).into());
        props.insert(Relation::new("true", vec![Constant::new("s").into()]).into());
        assert_eq!(next_state, State::from_props(props))
    }

    #[test]
    fn test_recursive1() {
        let (prover, init_state) = construct_prover("resources/nim-recursive1.gdl");
        let role = Role::new("white");

        let mut expected_moves = HashSet::new();
        for i in 0..2 {
           expected_moves.insert(Move::new(
               Function::new("reduce", vec![Constant::new("a").into(),
                                            Constant::new(i.to_string()).into()]).into()));
        }
        for i in 0..5 {
            expected_moves.insert(Move::new(
                Function::new("reduce",
                              vec![Constant::new("c").into(),
                                   Constant::new(i.to_string()).into()]).into()));
        }

        let results = prover.ask(query_builder::legal_query(&role), &init_state).into_moves();
        let results_len = results.len();
        let results_set: HashSet<Move> = results.into_iter().collect();
        assert_eq!(results_set.len(), results_len);
        assert_eq!(results_set, expected_moves);
    }

    #[test]
    fn test_recursive2() {
        let (prover, init_state) = construct_prover("resources/nim-recursive2.gdl");
        let role = Role::new("white");

        let mut expected_moves = HashSet::new();
        for i in 0..2 {
           expected_moves.insert(Move::new(
               Function::new("reduce", vec![Constant::new("a").into(),
                                            Constant::new(i.to_string()).into()]).into()));
        }
        for i in 0..5 {
            expected_moves.insert(Move::new(
                Function::new("reduce",
                              vec![Constant::new("c").into(),
                                   Constant::new(i.to_string()).into()]).into()));
        }

        let results = prover.ask(query_builder::legal_query(&role), &init_state).into_moves();
        let results_len = results.len();
        let results_set: HashSet<Move> = results.into_iter().collect();
        assert_eq!(results_set.len(), results_len);
        assert_eq!(results_set, expected_moves);
    }

    #[test]
    fn test_recursive() {
        let (prover, init_state) = construct_prover("resources/recursive.gdl");
        let role = Role::new("you");

        let mut expected_moves = HashSet::new();
        expected_moves.insert(Move::new(Constant::new("proceed").into()));
        let results = prover.ask(query_builder::legal_query(&role), &init_state).into_moves();
        let results_len = results.len();
        let results_set: HashSet<Move> = results.into_iter().collect();
        assert_eq!(results_set.len(), results_len);
        assert_eq!(results_set, expected_moves);
    }

    #[cfg(feature = "unstable")]
    mod bench {
        extern crate test;

        use self::test::Bencher;

        use super::construct_prover;
        use super::super::query_builder;
        use game_manager::State;
        use util::create_does;
        use gdl::Role;

        #[bench]
        fn bench_tictactoe7_legal(b: &mut Bencher) {
            let (prover, init_state) = construct_prover("resources/tictactoe7.gdl");
            let role = Role::new("white");

            b.iter(||
                   prover.ask(query_builder::legal_query(&role), &init_state));
        }

        #[bench]
        fn bench_tictactoe7_next(b: &mut Bencher) {
            let (prover, init_state) = construct_prover("resources/tictactoe7.gdl");
            let role = Role::new("white");
            let m = prover.ask(query_builder::legal_query(&role),
                               &init_state).into_moves();
            let mut props = init_state.props().clone();
            props.insert(create_does(&role, &m[0]));
            let init_state = State::from_props(props);

            b.iter(||
                   prover.ask(query_builder::next_query(), &init_state));
        }

        #[bench]
        fn bench_eightpuzzle(b: &mut Bencher) {
            let (prover, init_state) = construct_prover("resources/eightpuzzle.gdl");
            let role = Role::new("robot");

            b.iter(||
                   prover.ask(query_builder::legal_query(&role), &init_state));
        }

        #[bench]
        fn bench_ruledepthexponential(b: &mut Bencher) {
            let (prover, init_state) = construct_prover("resources/ruledepthexponential.gdl");
            let role = Role::new("robot");

            b.iter(||
                   prover.ask(query_builder::legal_query(&role), &init_state));
        }
    }
}
