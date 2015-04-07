use std::collections::{HashMap, HashSet};

use Player;
use prover::{self, query_builder};
use gdl::{self, Description, Sentence, Role, Move, Score, Function, Constant};
use gdl::Clause::SentenceClause;
use gdl::Sentence::{RelSentence, PropSentence};
use gdl::Term::{ConstTerm, FuncTerm};

use self::MatchState::{Started, Playing, Finished};

#[derive(Eq, PartialEq)]
pub enum MatchState {
    Started, Playing, Finished
}

pub struct Game {
    match_state: MatchState,
    roles: Vec<Role>,
    role: Role,
    start_clock: u32,
    play_clock: u32,
    cur_state: State,
    init_state: State,
}

#[derive(Clone)]
pub struct State {
    props: HashSet<Sentence>
}

impl State {
    fn new() -> State {
        State { props: HashSet::new() }
    }
}

impl Game {
    pub fn new(role: Role, start_clock: u32, play_clock: u32, desc: Description) -> Game {
        let roles = Game::compute_roles(&desc);
        let init_state = prover::ask(query_builder::init_query(), &State::new()).into_state();

        Game { match_state: Started, roles: roles, role: role, start_clock: start_clock,
               play_clock: play_clock, init_state: init_state.clone(), cur_state: init_state }
    }

    fn compute_roles(desc: &Description) -> Vec<Role> {
        let mut roles = Vec::new();
        for clause in desc.clauses.iter() {
            if let &SentenceClause(ref s) = clause {
                if let &RelSentence(ref r) = s {
                    if r.name.name == "role" {
                        roles.push(Role::new(r.name.name.to_string()))
                    }
                }
            }
        }
        roles
    }

    pub fn is_terminal(&self, state: &State) -> bool {
        prover::prove(query_builder::terminal_query(), state)
    }

    pub fn get_roles(&self) -> &Vec<Role> {
        &self.roles
    }

    pub fn get_role(&self) -> &Role {
        &self.role
    }

    pub fn get_initial_state(&self) -> &State {
        &self.init_state
    }

    pub fn get_current_state(&self) -> &State {
        &self.cur_state
    }

    pub fn get_legal_moves(&self, state: &State, role: &Role) -> Vec<Move> {
        prover::ask(query_builder::legal_query(role), state).into_moves()
    }

    pub fn get_legal_joint_moves(&self, state: &State) -> Vec<Vec<Move>> {
        panic!("unimplemented")
    }

    pub fn get_goals(&self, state: &State) -> Vec<Score> {
        let mut res = Vec::new();
        for role in self.roles.iter() {
            res.push(self.get_goal(state, role))
        }
        res
    }

    pub fn get_goal(&self, state: &State, role: &Role) -> Score {
        prover::ask(query_builder::goal_query(role), state).into_score()
    }

    pub fn get_next_states(&self, state: &State) -> Vec<State> {
        let mut res = Vec::new();
        for moves in self.get_legal_joint_moves(state) {
            res.push(self.get_next_state(state, moves));
        }
        res
    }

    pub fn get_next_state(&self, state: &State, moves: Vec<Move>) -> State {
        let s = state.clone();
        // TODO: Add moves to s
        prover::ask(query_builder::next_query(), &s).into_state()
    }

    pub fn get_start_clock(&self) -> u32 {
        self.start_clock
    }

    pub fn get_play_clock(&self) -> u32 {
        self.play_clock
    }

    fn update(&mut self, moves: Vec<Move>) {
        if self.match_state != Playing {
            self.match_state = Playing;
        }
        self.cur_state = self.get_next_state(&self.cur_state, moves);
    }

    fn finish(&mut self, moves: Vec<Move>) {
        self.cur_state = self.get_next_state(&self.cur_state, moves);
        self.match_state = Finished;
    }
}

pub struct GameManager<P> {
    player: P,
    games: HashMap<String, Game>
}

impl<P: Player> GameManager<P> {
    pub fn new(p: P) -> GameManager<P> {
        GameManager { games: HashMap::new(), player: p }
    }

    pub fn handle(&mut self, request: String) -> String {
        // TODO: Merge these
        let start_re = regex!(r"\(start ([^ ]+) ([^ ]+) (\(.*\)) (\d+) (\d+)\)");
        if let Some(caps) = start_re.captures(&request) {
            assert_eq!(caps.len(), 6);
            return self.handle_start(caps.at(1).unwrap(), caps.at(2).unwrap(), caps.at(3).unwrap(),
                              caps.at(4).unwrap().parse().unwrap(),
                              caps.at(5).unwrap().parse().unwrap());
        }
        let play_re = regex!(r"\(play ([^ ]+) (\(.*\))\)");
        if let Some(caps) = play_re.captures(&request) {
            assert_eq!(caps.len(), 3);
            return self.handle_play(caps.at(1).unwrap(), caps.at(2).unwrap());
        }
        let stop_re = regex!(r"\(stop ([^ ]+) (\(.*\))\)");
        if let Some(caps) = stop_re.captures(&request) {
            assert_eq!(caps.len(), 3);
            return self.handle_stop(caps.at(1).unwrap(), caps.at(2).unwrap());
        }
        "".to_string()
    }

    fn handle_start(&mut self, match_id: &str, role: &str, game_desc: &str,
                    start_clock: u32, play_clock: u32) -> String {
        debug!("Handling start request");
        let desc = gdl::parse(game_desc);
        let game = Game::new(Role::new(role.to_string()), start_clock, play_clock, desc);
        self.player.meta_game(&game);
        self.games.insert(match_id.to_string(), game);
        "ready".to_string()
    }

    fn handle_play(&mut self, match_id: &str, moves: &str) -> String {
        debug!("Handling play request");
        let game = self.games.get_mut(match_id).unwrap();
        let moves = parse_moves(moves);
        game.update(moves);
        let m = self.player.select_move(game);
        m.to_string()
    }

    fn handle_stop(&mut self, match_id: &str, moves: &str) -> String {
        debug!("Handling stop request");
        let game = self.games.get_mut(match_id).unwrap();
        let moves = parse_moves(moves);
        game.finish(moves);
        self.player.stop(game);
        "done".to_string()
    }
}

fn parse_moves(moves_str: &str) -> Vec<Move> {
    // Convert to valid GDL by adding a relation name
    assert_eq!(moves_str.char_at(0), '(');
    let mut moves_str = moves_str.to_string();
    moves_str.insert(1, 'a');
    moves_str.insert(2, ' ');

    let mut gdl = gdl::parse(&moves_str);
    assert_eq!(gdl.clauses.len(), 1);
    let clause = gdl.clauses.swap_remove(0);
    let mut moves = Vec::new();
    match clause {
        SentenceClause(s) => match s {
            RelSentence(r) => moves.push(Move::new(FuncTerm(Function::new(r.name, r.args)))),
            PropSentence(p) => moves.push(Move::new(ConstTerm(p.name))),
        },
        RuleClause => panic!("Expected sentence, got rule")
    }
    moves
}
