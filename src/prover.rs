use std::collections::HashSet;

use game_manager::State;
use gdl::{Sentence, Move};

pub fn ask(s: Sentence, state: State) -> QueryResult {
    panic!("unimplemented")
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
}

pub mod query_builder {
    use gdl::{Sentence, Relation, Constant, Variable};
    use gdl::Sentence::RelSentence;
    use gdl::Term::VarTerm;

    pub fn next_query() -> Sentence {
        RelSentence(Relation::new(Constant::new("next".to_string()),
                                  vec![VarTerm(Variable::new(Constant::new("x".to_string())))]))
    }
}
