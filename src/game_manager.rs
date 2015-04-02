use std::collections::HashMap;

use Player;

use gdl::{self, Rule, Role, Move, Score, GameDesc};
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
    bases: Vec<Rule>,
    input: Vec<Rule>,
    legal: Vec<Rule>,
    next: Vec<Rule>,
    terminal: Vec<Rule>,
    goal: Vec<Rule>,
    init_state: State,
    cur_state: State
}

#[derive(Clone)]
pub struct State;

impl Game {
    pub fn new(role: Role, start_clock: u32, play_clock: u32, roles: Vec<Role>, bases: Vec<Rule>,
           input: Vec<Rule>, legal: Vec<Rule>, next: Vec<Rule>, terminal: Vec<Rule>,
           goal: Vec<Rule>, init_state: State) -> Game {
        Game { match_state: Started, roles: roles, role: role, start_clock: start_clock,
               play_clock: play_clock, bases: bases, input: input, legal: legal, next: next,
               terminal: terminal, goal: goal, init_state: init_state.clone(),
               cur_state: init_state }
    }

    pub fn is_terminal(&self, state: State) -> bool {
        false
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
        Vec::new()
    }

    pub fn get_goals(&self, state: &State, role: &Role) -> Vec<Score> {
        Vec::new()
    }

    pub fn get_goal(&self, state: &State, role: &Role) -> Score {
        0
    }

    pub fn get_next_states(&self, state: &State) -> Vec<State> {
        Vec::new()
    }

    pub fn get_next_state(&self, state: &State, moves: Vec<Move>) -> State {
        State
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
    }

    fn finish(&mut self, moves: Vec<Move>) {
        self.update(moves);
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
        let GameDesc(roles, bases, input, legal, next, terminal, goal, init_state)
            = gdl::parse(game_desc);
        let game = Game::new(Role::new(role), start_clock, play_clock, roles, bases, input,
                             legal, next, terminal, goal, init_state);
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
