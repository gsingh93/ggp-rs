use std::collections::HashSet;

use game_manager::State;
use gdl::{Sentence, Move, Score};

pub fn ask(s: Sentence, state: &State) -> QueryResult {
    panic!("unimplemented")
}

pub fn prove(s: Sentence, state: &State) -> bool {
    !ask(s, state).props.is_empty()
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
