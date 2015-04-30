extern crate rand;
extern crate ggp_rs;

use ggp_rs::{Player, Game, Move};
use std::net::Ipv4Addr;

struct RandomPlayer;

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

fn main() {
    ggp_rs::run((Ipv4Addr::new(0,0,0,0), 9147), RandomPlayer);
}
