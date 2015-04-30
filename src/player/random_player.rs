extern crate rand;

use Player;
use game_manager::Game;
use gdl::Move;

pub struct RandomPlayer;
impl Player for RandomPlayer {
    fn get_name(&self) -> String {
        "RandomPlayer".to_string()
    }

    fn select_move(&mut self, game: &Game) -> Move {
        let state = game.get_current_state();
        let role = game.get_role();
        let mut moves = game.get_legal_moves(state, role);
        let r = rand::random::<usize>() % moves.len();
        moves.swap_remove(r)
    }
}
