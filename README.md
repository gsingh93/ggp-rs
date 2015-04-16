ggp-rs [![Build Status](https://travis-ci.org/gsingh93/ggp-rs.svg?branch=master)](https://travis-ci.org/gsingh93/ggp-rs)
======

**Note**: This library is currently not building on the nightly due to [a bug in Rust](https://github.com/rust-lang/rust/issues/24292). To use this library, you must use nightly-2015-04-13. The easiest way to install this nightly is with [multirust](https://github.com/brson/multirust).

`ggp-rs` is a library for creating GGP (general game playing) players in Rust that is based off of [GGP Base](https://github.com/ggp-org/ggp-base). While GGP Base allows the creation of players backed by a propositional network or a logic prover, this library currently only supports logic prover based players. Note that while this library is functional, it is still in early development. That means that the API may change, there are likely to be bugs, and there may be performance issues. Please file an [issue](https://github.com/gsingh93/ggp-rs/issues) to report a bug or request a feature. Pull requests are welcome.

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
    ggp_rs::run((Ipv4Addr::new(0,0,0,0), 9147), RandomPlayer);
}
```

To test the player you can use the `Server` application in GGP Base or make an account on [Tiltyard](http://tiltyard.ggp.org/) and add your player. Note that you should run your player with `cargo run --release` or your player may not be fast enough for most games.

### Documentation

You can find the API documentation [here](https://gsingh93.github.io/ggp-rs/doc/ggp_rs/).

### License

[MIT](https://github.com/gsingh93/ggp-rs/blob/master/LICENSE.txt)
