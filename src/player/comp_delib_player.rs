extern crate time;

use {Player, MoveResult};
use game_manager::{Game, State};
use gdl::{Move, Score};

/// A bounded compulsive deliberation player. This should only be used for single player games
pub struct CompDelibPlayer {
    depth_limit: u32,
    best_move: Option<Move>,
}

impl CompDelibPlayer {
    /// Returns a CompDelibPlayer that does not recurse past the given depth
    pub fn new(depth: u32) -> CompDelibPlayer {
        CompDelibPlayer { depth_limit: depth, best_move: None }
    }

    fn best_move(&mut self, game: &Game) -> MoveResult<Move> {
        let cur_state = game.current_state();
        let mut moves = game.legal_moves(cur_state, game.role());
        assert!(moves.len() >= 1, "No legal moves");

        if moves.len() == 1 {
            return Ok(moves.swap_remove(0));
        }

        let mut max = 0;
        let mut res = moves[0].clone();
        self.best_move = Some(res.clone());
        for m in moves {
            let score = match self.max_score(game, &cur_state, &vec![m.clone()], 0) {
                Ok(score) => score,
                Err(m) => return Err(m)
            };
            if score == 100 {
                return Ok(m);
            }
            if score > max {
                max = score;
                self.best_move = Some(m.clone());
                res = m;
            }
            check_time_result!(self, game);
        }
        Ok(res)
    }

    fn max_score(&mut self, game: &Game, state: &State, moves: &[Move],
                 depth: u32) -> MoveResult<Score> {
        if depth > self.depth_limit {
            return Ok(game.goal(state, game.role()));
        }

        let cur_state = game.next_state(state, moves);
        if game.is_terminal(&cur_state) {
            return Ok(game.goal(&cur_state, game.role()));
        }

        let moves = game.legal_moves(&cur_state, game.role());
        assert!(moves.len() >= 1, "No legal moves");

        let mut max = 0;
        for m in moves {
            let score = match self.max_score(game, &cur_state, &vec![m], depth + 1) {
                Ok(score) => score,
                e @ Err(_) => return e
            };
            if score > max {
                max = score
            }
            check_time_result!(self, game);
        }
        Ok(max)
    }
}

impl Player for CompDelibPlayer {
    fn name(&self) -> String {
        "CompDelibPlayer".to_string()
    }

    fn select_move(&mut self, game: &Game) -> Move {
        assert!(game.roles().len() == 1,
                "CompDelibPlayer only works with single player games");
        let m = match self.best_move(&game) {
            Ok(m) => m,
            Err(m) => { warn!("Out of time"); m }
        };
        info!("Selecting move {}", m.to_string());
        m
    }

    fn out_of_time(&mut self, _: &Game) -> Move {
        self.best_move.take().unwrap()
    }
}
