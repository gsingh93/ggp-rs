extern crate time;
extern crate rand;

use {Player, MoveResult};
use game_manager::{Game, State};
use gdl::{Move, Score, Role};

use std::cmp::{max, min};

/// A Monte Carlo search player. This player should only be used for 2 player, constant sum,
/// turn based games.
pub struct McsPlayer {
    depth_limit: u32,
    best_move: Option<Move>,
    charge_count: u32,
}

impl McsPlayer {
    /// Returns an McsPlayer that begins the random terminal state searches at depth `depth`
    pub fn new(depth: u32, charge_count: u32) -> McsPlayer {
        McsPlayer { depth_limit: depth, best_move: None, charge_count: charge_count }
    }

    fn best_move(&mut self, game: &Game) -> MoveResult<Move> {
        let role = game.role();
        let cur_state = game.current_state();
        let mut moves = game.legal_moves(cur_state, role);
        assert!(!moves.is_empty(), "No legal moves");

        if moves.len() == 1 {
            return Ok(moves.swap_remove(0));
        }

        let mut res = moves[0].clone();
        self.best_move = Some(res.clone());

        let mut max = 0;
        self.best_move = Some(res.clone());
        let opponent = opponent(game, role);
        for m in moves {
            let score = match self.min_score(game, cur_state, opponent, m.clone(), 0, 100, 0) {
                Ok(score) => score,
                Err(m) => return Err(m)
            };
            if score == 100 {
                return Ok(m);
            } else if score > max {
                max = score;
                self.best_move = Some(m.clone());
                res = m
            }
            check_time_result!(self, game);
        }
        Ok(res)
    }

    fn max_score(&mut self, game: &Game, state: &State, role: &Role, alpha: u8, beta: u8,
                 depth: u32) -> MoveResult<Score> {
        if depth >= self.depth_limit {
            return self.monte_carlo(role, game, state);
        }

        if game.is_terminal(state) {
            return Ok(game.goal(state, game.role()));
        }

        let moves = game.legal_moves(state, role);
        assert!(!moves.is_empty(), "No legal moves");

        let opponent = opponent(game, role);
        let mut alpha = alpha;
        for m in moves {
            let res = match self.min_score(game, state, &opponent, m, alpha, beta, depth + 1) {
                Ok(score) => score,
                e @ Err(_) => return e
            };

            alpha = max(res, alpha);
            if alpha >= beta {
                return Ok(beta);
            }
            check_time_result!(self, game);
        }
        Ok(alpha)
    }

    fn min_score(&mut self, game: &Game, state: &State, role: &Role, last_move: Move, alpha: u8,
                 beta: u8, depth: u32) -> MoveResult<Score> {
        let moves = game.legal_moves(state, role);
        assert!(moves.len() >= 1, "No legal moves");

        let mut beta = beta;
        for m in moves {
            let move_vec = if game.roles()[0] == *role {
                vec![m, last_move.clone()]
            } else {
                vec![last_move.clone(), m]
            };
            let s = game.next_state(state, &*move_vec);
            let opponent = opponent(game, role);
            let res = match self.max_score(game, &s, &opponent, alpha, beta, depth) {
                Ok(score) => score,
                e @ Err(_) => return e
            };
            beta = min(res, beta);
            if beta <= alpha {
                return Ok(alpha);
            }
            check_time_result!(self, game);
        }
        Ok(beta)
    }

    fn monte_carlo(&mut self, role: &Role, game: &Game, state: &State) -> MoveResult<Score> {
        let mut total: u32 = 0;
        for _ in 0..self.charge_count {
            match self.depth_charge(role, game, state) {
                Ok(res) => total += res as u32,
                Err(e) => return Err(e)
            }
        }
        Ok((total / self.charge_count) as u8)
    }

    fn depth_charge(&mut self, role: &Role, game: &Game, state: &State) -> MoveResult<Score> {
        let mut new_state = state.clone();
        let mut moves = Vec::with_capacity(game.roles().len());
        while !game.is_terminal(&new_state) {
            moves.clear();
            for r in game.roles().into_iter() {
                let mut legals = game.legal_moves(&new_state, r);
                let r = rand::random::<usize>() % legals.len();
                moves.push(legals.swap_remove(r));
            }

            new_state = game.next_state(&new_state, &moves);
            check_time_result!(self, game);
        }
        return Ok(game.goal(state, role));
    }
}

fn opponent<'a>(game: &'a Game, role: &'a Role) -> &'a Role {
    let roles = game.roles();
    assert!(roles.len() == 2, "Must be a two player game");
    let res: Vec<_> = roles.into_iter().filter(|r| *r != role).collect();
    assert_eq!(res.len(), 1);
    res[0]
}

impl Player for McsPlayer {
    fn name(&self) -> String {
        "McsPlayer".to_string()
    }

    fn select_move(&mut self, game: &Game) -> Move {
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
