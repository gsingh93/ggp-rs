extern crate rand;
extern crate ggp_rs;

use ggp_rs::{Player, Game, Move};
use std::net::Ipv4Addr;

struct RandomPlayer;

impl Player for RandomPlayer {
    fn get_name(&self) -> String {
        "RandomPlayer".to_string()
    }

    fn select_move(&self, game: &Game) -> Move {
        let state = game.get_current_state();
        let role = game.get_role();
        let mut moves = game.get_legal_moves(state, role);
        let r = rand::random::<usize>() % moves.len();
        moves.swap_remove(r)
    }
}

fn main() {
    ggp_rs::run((Ipv4Addr::new(127,0,0,1), 3000), RandomPlayer);
}
