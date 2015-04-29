use std::fmt::{Display, Debug, Formatter, Error};

pub use gdl_parser::{Description, Clause, Rule, Sentence, Term, Literal, Constant, Variable,
                     Function, Relation, Proposition, Not, Or, Distinct};
pub use gdl_parser::parse;

#[allow(unused)]
pub mod constants {
    use gdl::{Constant, Move};

    lazy_static! {
        pub static ref TRUE_CONST: Constant = Constant::new("true");
        pub static ref DOES_CONST: Constant = Constant::new("does");
        pub static ref NEXT_CONST: Constant = Constant::new("next");
        pub static ref LEGAL_CONST: Constant = Constant::new("legal");
        pub static ref GOAL_CONST: Constant = Constant::new("goal");
        pub static ref TERMINAL_CONST: Constant = Constant::new("terminal");
        pub static ref NIL_MOVE: Move = Move::new(Constant::new("nil").into());
    }
}

/// The score a player can get at a goal state
pub type Score = u8;

#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub struct Role {
    name: String
}

impl Role {
    pub fn new<T: Into<String>>(name: T) -> Role {
        Role { name: name.into() }
    }

    pub fn name(&self) -> &str {
        &self.name
    }
}

#[derive(Clone, Eq, PartialEq, Hash)]
pub struct Move {
    pub contents: Term
}

impl Move {
    pub fn new(t: Term) -> Move {
        Move { contents: t }
    }
}

impl Display for Move {
    fn fmt(&self, f: &mut Formatter) -> Result<(), Error> {
        write!(f, "{}", self.contents.to_string())
    }
}

impl Debug for Move {
    fn fmt(&self, f: &mut Formatter) -> Result<(), Error> {
        Display::fmt(self, f)
    }
}
