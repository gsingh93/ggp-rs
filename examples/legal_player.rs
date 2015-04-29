extern crate ggp_rs;

use ggp_rs::{Player, Game, Move};
use std::net::Ipv4Addr;

struct LegalPlayer;

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

fn main() {
    ggp_rs::run((Ipv4Addr::new(0,0,0,0), 9147), LegalPlayer);
}
