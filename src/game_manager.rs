use std::collections::{HashMap, HashSet};

use Player;
use prover::{self, query_builder};
use gdl::{self, Description, Sentence, Role, Move, Score};
use gdl::Clause::SentenceClause;
use gdl::Sentence::RelSentence;

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
    cur_state: State
}

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
        let init_state = prover::ask(query_builder::next_query(), State::new()).into_state();

        Game { match_state: Started, roles: roles, role: role, start_clock: start_clock,
               play_clock: play_clock, cur_state: init_state }
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

    pub fn is_terminal(&self, state: State) -> bool {
        panic!("unimplemented")
    }

    pub fn get_roles(&self) -> &Vec<Role> {
        &self.roles
    }

    pub fn get_role(&self) -> &Role {
        &self.role
    }

    pub fn get_initial_state(&self) -> &State {
        panic!("unimplemented")
    }

    pub fn get_current_state(&self) -> &State {
        &self.cur_state
    }

    pub fn get_legal_moves(&self, state: &State, role: &Role) -> Vec<Move> {
        panic!("unimplemented")
    }

    pub fn get_legal_joint_moves(&self, state: &State, role: &Role) -> Vec<Vec<Move>> {
        panic!("unimplemented")
    }

    pub fn get_goals(&self, state: &State) -> HashMap<Role, Score> {
        panic!("unimplemented")
    }

    pub fn get_goal(&self, state: &State, role: &Role) -> Score {
        panic!("unimplemented")
    }

    pub fn get_next_states(&self, state: &State) -> Vec<State> {
        panic!("unimplemented")
    }

    pub fn get_next_state(&self, state: &State, moves: Vec<Move>) -> State {
        panic!("unimplemented")
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
        game.update(Vec::new()); // TODO
        let m = self.player.select_move(game);
        m.to_string()
    }

    fn handle_stop(&mut self, match_id: &str, moves: &str) -> String {
        debug!("Handling stop request");
        let game = self.games.get_mut(match_id).unwrap();
        game.finish(Vec::new()); // TODO
        self.player.stop(game);
        "done".to_string()
    }
}
