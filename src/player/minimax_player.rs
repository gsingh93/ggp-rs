use Player;
use game_manager::{Game, State};
use gdl::{Move, Score, Role};

/// A bounded minimax player. This player should only be used for 2 player, constant sum,
/// turn based games.
pub struct MinimaxPlayer {
    min_bound: u8,
    max_bound: u8
}

impl Player for MinimaxPlayer {
    fn name(&self) -> String {
        "MinimaxPlayer".to_string()
    }

    fn select_move(&mut self, game: &Game) -> Move {
        let m = self.best_move(&game);
        info!("Selecting move {}", m.to_string());
        m
    }
}

impl MinimaxPlayer {
    /// Returns a minimax player with the default bounds of 0 and 100
    pub fn new() -> MinimaxPlayer {
        MinimaxPlayer { min_bound: 0, max_bound: 100 }
    }

    /// Returns a minimax player with the given min and max bounds
    pub fn with_bounds(min_bound: u8, max_bound: u8) -> MinimaxPlayer {
        MinimaxPlayer { min_bound: min_bound, max_bound: max_bound }
    }

    fn best_move(&self, game: &Game) -> Move {
        let role = game.role();
        let cur_state = game.current_state();
        let moves = game.legal_moves(cur_state, role);
        assert!(moves.len() >= 1, "No legal moves");

        let mut max = 0;
        let mut res = moves[0].clone();
        let opponent = opponent(game, role);
        for m in moves {
            let score = self.min_score(game, cur_state, &opponent, m.clone());
            if score >= self.max_bound {
                return m;
            } else if score > max {
                max = score;
                res = m
            }
        }
        res
    }

    fn max_score(&self, game: &Game, state: &State, role: &Role) -> Score {
        if game.is_terminal(state) {
            return game.goal(state, game.role());
        }

        let moves = game.legal_moves(state, role);
        assert!(moves.len() >= 1, "No legal moves");

        let mut max = 0;
        let opponent = opponent(game, role);
        for m in moves {
            let score = self.min_score(game, state, &opponent, m);
            if score >= self.max_bound {
                return score;
            } else if score > max {
                max = score;
            }
        }
        max
    }

    fn min_score(&self, game: &Game, state: &State, role: &Role, last_move: Move) -> Score {
        let moves = game.legal_moves(state, role);
        assert!(moves.len() >= 1, "No legal moves");

        let mut min = 100;
        for m in moves {
            let move_vec = if game.roles()[0] == *role {
                vec![m, last_move.clone()]
            } else {
                vec![last_move.clone(), m]
            };
            let s = game.next_state(state, &*move_vec);
            let opponent = opponent(game, role);
            let score = self.max_score(game, &s, &opponent);
            if score <= self.min_bound {
                return score;
            } else if score < min {
                min = score;
            }
        }
        min
    }
}

fn opponent(game: &Game, role: &Role) -> Role {
    let roles = game.roles();
    assert!(roles.len() == 2, "Must be a two player game");
    for r in roles {
        if role != r {
            return (*r).clone();
        }
    }
    panic!("Shouldn't happen");
}
