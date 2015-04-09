use std::collections::{HashMap, HashSet};

use Player;
use prover::{Prover, query_builder};
use gdl::{self, Description, Sentence, Role, Move, Score, Function, Constant, Relation};
use gdl::Clause::{SentenceClause, RuleClause};
use gdl::Sentence::{RelSentence, PropSentence};

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
    prover: Prover
}

#[derive(Debug, Clone)]
pub struct State {
    pub props: HashSet<Sentence>
}

impl State {
    pub fn new() -> State {
        State { props: HashSet::new() }
    }
}

impl Game {
    pub fn new(role: Role, start_clock: u32, play_clock: u32, desc: Description) -> Game {
        let roles = Game::compute_roles(&desc);
        let prover = Prover::new(desc);
        let init_state = prover.ask(query_builder::init_query(), State::new()).into_state();

        Game { match_state: Started, roles: roles, role: role, start_clock: start_clock,
               play_clock: play_clock, init_state: init_state.clone(), cur_state: init_state,
               prover: prover }
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
        self.prover.prove(query_builder::terminal_query(), (*state).clone())
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
        self.prover.ask(query_builder::legal_query(role), (*state).clone()).into_moves()
    }

    pub fn get_legal_joint_moves(&self, state: &State) -> Vec<Vec<Move>> {
        let mut legal_moves = Vec::new();
        for role in self.roles.iter() {
            legal_moves.push(self.get_legal_moves(state, role));
        }

        cross_product(legal_moves)
    }

    pub fn get_goals(&self, state: &State) -> Vec<Score> {
        let mut res = Vec::new();
        for role in self.roles.iter() {
            res.push(self.get_goal(state, role))
        }
        res
    }

    pub fn get_goal(&self, state: &State, role: &Role) -> Score {
        self.prover.ask(query_builder::goal_query(role), (*state).clone()).into_score()
    }

    pub fn get_next_states(&self, state: &State) -> Vec<State> {
        let mut res = Vec::new();
        for moves in self.get_legal_joint_moves(state) {
            res.push(self.get_next_state(state, &moves));
        }
        res
    }

    pub fn get_next_state(&self, state: &State, moves: &[Move]) -> State {
        if moves[0] == Move::new(Constant::new("nil").into()) {
            return state.clone();
        }
        assert_eq!(moves.len(), self.roles.len());
        let mut s = state.clone();
        for (m, r) in moves.iter().zip(self.roles.iter()) {
            s.props.insert(create_does(r, m));
        }

        self.prover.ask(query_builder::next_query(), s.clone()).into_state()
    }

    pub fn get_start_clock(&self) -> u32 {
        self.start_clock
    }

    pub fn get_play_clock(&self) -> u32 {
        self.play_clock
    }

    fn update(&mut self, moves: &[Move]) {
        if self.match_state != Playing {
            self.match_state = Playing;
        }
        self.cur_state = self.get_next_state(&self.cur_state, moves);
    }

    fn finish(&mut self, moves: &[Move]) {
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
        // TODO: This function is nasty
        let start_re = regex!(r"\(start ([^ ]+) ([^ ]+) \((.*)\) (\d+) (\d+)\)");
        if let Some(caps) = start_re.captures(&request) {
            assert_eq!(caps.len(), 6);
            return self.handle_start(caps.at(1).unwrap(), caps.at(2).unwrap(), caps.at(3).unwrap(),
                              caps.at(4).unwrap().parse().unwrap(),
                              caps.at(5).unwrap().parse().unwrap());
        }
        let play_re = regex!(r"\(play ([^ ]+) \(?(.*)\)?\)");
        if let Some(caps) = play_re.captures(&request) {
            assert_eq!(caps.len(), 3);
            return self.handle_play(caps.at(1).unwrap(), caps.at(2).unwrap());
        }

        let stop_re = regex!(r"\(stop ([^ ]+) \((.*)\)\)");
        if let Some(caps) = stop_re.captures(&request) {
            assert_eq!(caps.len(), 3);
            return self.handle_stop(caps.at(1).unwrap(), caps.at(2).unwrap());
        }
        panic!("request didn't match any regex");
    }

    fn handle_start(&mut self, match_id: &str, role: &str, game_desc: &str,
                    start_clock: u32, play_clock: u32) -> String {
        debug!("Handling start request");
        let desc = gdl::parse(game_desc.trim());
        let game = Game::new(Role::new(role.to_string()), start_clock, play_clock, desc);
        self.player.meta_game(&game);
        self.games.insert(match_id.to_string(), game);
        debug!("Sending 'ready'");
        "ready".to_string()
    }

    fn handle_play(&mut self, match_id: &str, moves: &str) -> String {
        debug!("Handling play request");
        let game = self.games.get_mut(match_id).expect("Match doesn't exist");
        let moves = parse_moves(moves);
        game.update(&moves);
        let m = self.player.select_move(game);
        let mov = m.to_string();
        debug!("Sending {}", mov);
        mov
    }

    fn handle_stop(&mut self, match_id: &str, moves: &str) -> String {
        debug!("Handling stop request");
        let game = self.games.get_mut(match_id).expect("Match doesn't exist");
        let moves = parse_moves(moves);
        game.finish(&moves);
        self.player.stop(game);
        debug!("Sending 'done'");
        "done".to_string()
    }
}

fn parse_moves(moves_str: &str) -> Vec<Move> {
    let gdl = gdl::parse(moves_str);
    let mut moves = Vec::new();
    for clause in gdl.clauses {
        let sentence = match clause {
            RuleClause(_) => panic!("Expected sentence, got rule"),
            SentenceClause(s) => s
        };
        match sentence {
            RelSentence(r) => moves.push(Move::new(Function::new(r.name, r.args).into())),
            PropSentence(p) => moves.push(Move::new(p.name.into()))
        }
    }
    moves
}

fn cross_product<T: Clone>(v: Vec<Vec<T>>) -> Vec<Vec<T>> {
    fn helper<'a, T: Clone>(v: &'a [Vec<T>], res: &mut Vec<Vec<T>>, partial: &mut Vec<&'a T>) {
        if v.len() == partial.len() {
            res.push(partial.iter().map(|x| (**x).clone()).collect());
        } else {
            assert!(partial.len() < v.len());
            for t in v[partial.len()].iter() {
                partial.push(t);
                helper(v, res, partial);
                partial.pop().unwrap();
            }
        }
    }

    let mut res = Vec::new();
    helper(&*v, &mut res, &mut Vec::new());
    res
}

fn create_does(r: &Role, m: &Move) -> Sentence {
    RelSentence(Relation::new(Constant::new("does"),
                              vec![Constant::new(r.name()).into(), m.contents.clone()]))
}

#[cfg(test)]
mod test {
    use Player;
    use super::{GameManager, Game};
    use gdl::Move;

    struct LegalPlayer;
    impl Player for LegalPlayer {
        fn get_name(&self) -> String {
            "LegalPlayer".to_string()
        }

        fn select_move(&self, game: &Game) -> Move {
            let state = game.get_current_state();
            let role = game.get_role();
            let mut moves = game.get_legal_moves(state, role);
            moves.swap_remove(0)
        }
    }

    #[test]
    fn test_play_nil() {
        let mut gm = GameManager::new(LegalPlayer);
        assert_eq!(
            &gm.handle("(start match_id black ((role black) (input noop) \
                        (legal black noop)) 10 5)".to_string()),
            "ready");
        assert_eq!(&gm.handle("(play match_id nil)".to_string()), "noop");
    }
}
