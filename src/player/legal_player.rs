use Player;
use game_manager::Game;
use gdl::Move;

/// A player that returns the first legal move it finds
pub struct LegalPlayer;

impl Player for LegalPlayer {
    fn name(&self) -> String {
        "LegalPlayer".to_string()
    }

    fn select_move(&mut self, game: &Game) -> Move {
        let state = game.current_state();
        let role = game.role();
        let mut moves = game.legal_moves(state, role);
        moves.swap_remove(0)
    }
}
