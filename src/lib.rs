//! A library for creating General Game Playing (GGP) players. This library is based off of
//! [GGP Base](https://github.com/ggp-org/ggp-base). While GGP Base allows the creation of
//! players backed by a propositional network or a logic prover, this library currently only
//! supports logic prover based players.
//!
//! # Example
//!
//! To create your own player, simply implement the `Player` trait for your struct and pass the
//! host/port you want the player to run at and the player itself to the `run` function.
//!
//! The following example implements a RandomPlayer, which plays random legal moves each turn.
//!
//! ```ignore
//! extern crate rand;
//! extern crate ggp_rs;
//!
//! use ggp_rs::{Player, Game, Move};
//! use std::net::Ipv4Addr;
//!
//! struct RandomPlayer;
//!
//! impl Player for RandomPlayer {
//!     fn get_name(&self) -> String {
//!         "RandomPlayer".to_string()
//!     }
//!
//!     fn select_move(&self, game: &Game) -> Move {
//!         let state = game.get_current_state();
//!         let role = game.get_role();
//!         let mut moves = game.get_legal_moves(state, role);
//!         let r = rand::random::<usize>() % moves.len();
//!         moves.swap_remove(r)
//!     }
//! }
//!
//! fn main() {
//!     ggp_rs::run((Ipv4Addr::new(0,0,0,0), 9147), RandomPlayer);
//! }
//! ```

#![feature(std_misc, plugin, collections)]
#![cfg_attr(test, feature(test))]
#![plugin(regex_macros)]

extern crate gdl_parser;
extern crate hyper;
extern crate regex;
extern crate unicase;

#[macro_use]
extern crate log;

mod game_manager;
mod gdl;
mod prover;

use unicase::UniCase;

use hyper::Server;
use hyper::server::{Request, Response, Handler};
use hyper::header::{ContentLength, ContentType, AccessControlAllowOrigin,
                    AccessControlAllowHeaders};
use hyper::net::Fresh;
use hyper::version::HttpVersion;

use std::net::ToSocketAddrs;
use std::io::Read;
use std::io::Write;
use std::ascii::OwnedAsciiExt;
use std::sync::Mutex;

use game_manager::GameManager;

pub use game_manager::{Game, State};
pub use gdl::{Move, Role, Score};

/// A GGP player
pub trait Player {
    fn get_name(&self) -> String;

    fn meta_game(&self, _: &Game) {}

    fn select_move(&self, game: &Game) -> Move;

    fn stop(&self, _: &Game) {}
}

/// Starts a GGP player listening at `host`
pub fn run<T: ToSocketAddrs + 'static, P: Player + Sync + Send + 'static>(host: T, player: P) {
    let handler = GameHandler::new(player);
    Server::http(handler).listen(host).unwrap();
}

struct GameHandler<P: Player + Send> {
    pub gm: Mutex<GameManager<P>>
}

impl<P: Player + Send> GameHandler<P> {
    pub fn new(player: P) -> GameHandler<P> {
        GameHandler { gm: Mutex::new(GameManager::new(player)) }
    }
}

impl<P: Player + Sync + Send> Handler for GameHandler<P> {
    fn handle(&self, mut req: Request, mut res: Response<Fresh>) {
        let mut s = String::new();
        req.read_to_string(&mut s).unwrap();
        let s = s.into_ascii_lowercase();
        info!("Got request: {}", s);

        let mut gm = self.gm.lock().unwrap();
        let s = gm.handle(s);
        let s = s.into_bytes();
        res.headers_mut().set(ContentLength(s.len() as u64));
        res.headers_mut().set(ContentType("text/acl".parse().unwrap()));
        res.headers_mut().set(AccessControlAllowOrigin::Any);
        res.headers_mut().set(AccessControlAllowHeaders(
            vec![UniCase("Content-Type".to_string())]));
        res.version = HttpVersion::Http10;
        let mut res = res.start().unwrap();
        res.write_all(&s).unwrap();
        res.end().unwrap();
    }
}
