use Player;
use game_manager::Game;
use gdl::Move;

pub struct LegalPlayer;
impl Player for LegalPlayer {
    fn get_name(&self) -> String {
        "LegalPlayer".to_string()
    }

    fn select_move(&mut self, game: &Game) -> Move {
        let state = game.get_current_state();
        let role = game.get_role();
        let mut moves = game.get_legal_moves(state, role);
        moves.swap_remove(0)
    }
}
