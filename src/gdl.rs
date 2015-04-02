use game_manager::State;

pub struct Rule;
pub struct Role {
    pub name: String
}

impl Role {
    pub fn new(name: &str) -> Role {
        Role { name: name.to_string() }
    }
}

pub struct Move;

impl ToString for Move {
    fn to_string(&self) -> String {
        "".to_string() // TODO
    }
}

pub type Score = u8;

pub struct GameDesc(pub Vec<Role>, pub Vec<Rule>, pub Vec<Rule>, pub Vec<Rule>, pub Vec<Rule>,
                    pub Vec<Rule>, pub Vec<Rule>, pub State);

pub fn parse(gdl: &str) -> GameDesc {
    GameDesc(Vec::new(), Vec::new(), Vec::new(), Vec::new(), Vec::new(), Vec::new(), Vec::new(),
             State)
}
