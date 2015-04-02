ggp-rs
======

`ggp-rs` is a library for creating GGP (general game playing) players in Rust. This library is a work in progress. Currently, this library can parse requests from the GGP server and send replies back. This includes parsing the KIF/GDL into an AST. However, the semantics/proving of the GDL has not been finished.

Here is an example of creating a player that plays random legal moves (this example can be found in the `examples` folder):

```
extern crate rand;
extern crate ggp_rs;

use ggp_rs::{Player, Game, Move};
use std::net::Ipv4Addr;

struct RandomLegalPlayer;

impl Player for RandomLegalPlayer {
    fn get_name(&self) -> String {
        "RandomLegalPlayer".to_string()
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
    ggp_rs::run((Ipv4Addr::new(127,0,0,1), 3000), RandomLegalPlayer);
}
```

You can use [this](http://sourceforge.net/projects/ggpserver/files/gamecontroller/) game manager to test the client.
