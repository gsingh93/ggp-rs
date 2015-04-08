pub use gdl_parser::{Description, Clause, Rule, Sentence, Term, Literal, Constant, Variable,
                     Function, Relation, Proposition, Not, Or, Distinct};
pub use gdl_parser::parse;

pub type Score = u8;

#[derive(Clone, Eq, PartialEq, Hash)]
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

impl ToString for Move {
    fn to_string(&self) -> String {
        self.contents.to_string()
    }
}
