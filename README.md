ggp-rs [![Build Status](https://travis-ci.org/gsingh93/ggp-rs.svg?branch=master)](https://travis-ci.org/gsingh93/ggp-rs) [![](https://meritbadge.herokuapp.com/ggp-rs)](https://crates.io/crates/ggp-rs)
======

`ggp-rs` is a library for creating GGP (general game playing) players in Rust that is based off of [GGP Base](https://github.com/ggp-org/ggp-base). While GGP Base allows the creation of players backed by a propositional network or a logic prover, this library currently only supports logic prover based players. The performance of this logic prover is comparable to the one in GGP Base.

Please file an [issue](https://github.com/gsingh93/ggp-rs/issues) to report a bug or request a feature. Pull requests are welcome.

### Installation

You can install this library from [crates.io](https://crates.io/) by adding the following to your `Cargo.toml`:

```
ggp-rs = "*"
```

### Example

Here is an example of a player that plays random legal moves (this example can be found in the `examples` folder):

```
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
```

To test the player you can use the `Server` application in GGP Base or make an account on [Tiltyard](http://tiltyard.ggp.org/) and add your player. Note that you should run your player with `cargo run --release` or your player may not be fast enough for most games.

More examples and players can be found in `src/player`.

Note that `ggp-rs` outputs logging information that you might find useful. It is recommend to set the log level to at least warnings and higher, and this can be increased to info (or debug, but debug is not recommended) for more information. To set the log levels to warning, initialize an `env_logger` and run cargo with the `RUST_LOG` variable, i.e. `RUST_LOG=ggp_rs=warn cargo run --release`.

### Documentation

You can find the API documentation [here](https://gsingh93.github.io/ggp-rs/ggp_rs/index.html).

### License

[MIT](https://github.com/gsingh93/ggp-rs/blob/master/LICENSE.txt)
