extern crate rand;

use Player;
use game_manager::Game;
use gdl::Move;

/// A player that chooses a random move from all possible of legal moves
pub struct RandomPlayer;

impl Player for RandomPlayer {
    fn name(&self) -> String {
        "RandomPlayer".to_string()
    }

    fn select_move(&mut self, game: &Game) -> Move {
        let state = game.current_state();
        let role = game.role();
        let mut moves = game.legal_moves(state, role);
        let r = rand::random::<usize>() % moves.len();
        moves.swap_remove(r)
    }
}
