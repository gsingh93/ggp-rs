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
//!     fn name(&self) -> String {
//!         "RandomPlayer".to_string()
//!     }
//!
//!     fn select_move(&mut self, game: &Game) -> Move {
//!         let state = game.current_state();
//!         let role = game.role();
//!         let mut moves = game.legal_moves(state, role);
//!         let r = rand::random::<usize>() % moves.len();
//!         moves.swap_remove(r)
//!     }
//! }
//!
//! fn main() {
//!     ggp_rs::run((Ipv4Addr::new(0,0,0,0), 9147), RandomPlayer);
//! }
//! ```

#![deny(missing_docs)]
#![cfg_attr(all(test, feature = "unstable"), feature(test))]

extern crate time;
extern crate gdl_parser;
extern crate hyper;
extern crate regex;
extern crate unicase;

#[macro_use]
extern crate log;

#[macro_use]
extern crate lazy_static;

/// This type meant to be used in GGP players for returning a move when time runs out. For
/// functions that would normally have a return type `T`, you can return a `MoveResult<T>` instead.
/// On normal execution, an `Ok(T)` can be returned, and when out of time an `Err(Move)` can
/// be returned. You can implement this logic yourself or just use the provided
/// `check_time_result!` macro.
pub type MoveResult<T> = Result<T, Move>;

/// Checks whether we are out of time, and if so, returns the move selected by
/// `Player::out_of_time`.
#[macro_export]
macro_rules! check_time {
    ($self_:ident, $game:ident) => (
        if $game.move_start_time().to(time::PreciseTime::now()) >
            time::Duration::milliseconds(
                (1000 * $game.play_clock() - $self_.cutoff()) as i64) {
            return $self_.out_of_time($game);
        });
}

/// Checks whether we are out of time, and if so, returns the move selected by
/// `Player::out_of_time` wrapped in a `MoveResult`.
#[macro_export]
macro_rules! check_time_result {
    ($self_:ident, $game:ident) => (
        if $game.move_start_time().to(time::PreciseTime::now()) >
            time::Duration::milliseconds(
                (1000 * $game.play_clock() - $self_.cutoff()) as i64) {
            return Err($self_.out_of_time($game));
        });
}

/// Ready to use GGP players
pub mod player;

mod util;
mod game_manager;
mod gdl;
mod prover;

use unicase::UniCase;

use hyper::Server;
use hyper::error::Error::Io;
use hyper::server::{Request, Response, Handler};
use hyper::header::{ContentLength, ContentType, AccessControlAllowOrigin,
                    AccessControlAllowHeaders};
use hyper::net::Fresh;
use hyper::version::HttpVersion;

use std::net::ToSocketAddrs;
use std::io::{Read, Write};
use std::sync::Mutex;
use std::ascii::AsciiExt;

use game_manager::GameManager;

pub use game_manager::{Game, State};
pub use gdl::{Move, Role, Score};

/// A GGP player
pub trait Player: Send {
    /// Returns the name of this player
    fn name(&self) -> String;

    /// Called after receiving a `start` message. Used to perform any computation before the start
    /// of the game.
    fn meta_game(&mut self, _: &Game) {}

    /// Called after receiving a `play` message. Returns a `Move` for this turn.
    fn select_move(&mut self, game: &Game) -> Move;

    /// The cutoff for the remaining time for the start or play clock in milliseconds, after which
    /// `out_of_time` should be called. Note that this function does not call `out_of_time`, but is
    /// simply used by other functions when deciding whether to call it. Defaults to 500
    /// milliseconds.
    fn cutoff(&self) -> u32 { 500 }

    /// Gets a move to play when there is no more time left for computation. While it is not
    /// required that clients implement this function to use the `Player` trait, the default
    /// implementation will panic. This is so players that do not want to use this feature can
    /// ignore it. Instead of calling this function directly, you can use the `check_time!` and
    /// `check_time_result!` macros.
    fn out_of_time(&mut self, _: &Game) -> Move { unimplemented!() }

    /// Called when a game is finished or aborted
    fn stop(&mut self, _: &Game) {}
}

/// Starts a GGP player listening at `host`
pub fn run<T: ToSocketAddrs + 'static, P: Player + 'static>(host: T, player: P) {
    let handler = GameHandler::new(player);
    match Server::http(handler).listen(host) {
        Err(Io(e)) => panic!("{}", e),
        Err(e) => panic!("{}", e),
        _ => ()
    }
}

struct GameHandler<P: Player> {
    pub gm: Mutex<GameManager<P>>
}

impl<P: Player> GameHandler<P> {
    pub fn new(player: P) -> GameHandler<P> {
        GameHandler { gm: Mutex::new(GameManager::new(player)) }
    }
}

// This is unsafe because `GameManager` contains `Rc`s. If we're careful, we can use these `Rc`s
// safely and not have to resort to `Arc`s, which are slower.
unsafe impl<P: Player> Send for GameManager<P> {}

impl<P: Player> Handler for GameHandler<P> {
    fn handle(&self, mut req: Request, mut res: Response<Fresh>) {
        let mut req_str = String::new();
        req.read_to_string(&mut req_str).unwrap();
        let req_str = req_str.to_ascii_lowercase(); // TODO: Avoid allocation
        info!("Got request: {}", req_str);

        let response = {
            let mut gm = self.gm.lock().unwrap();
            gm.handle(req_str)
        };
        let response = response.into_bytes();
        res.headers_mut().set(ContentLength(response.len() as u64));
        res.headers_mut().set(ContentType("text/acl".parse().unwrap()));
        res.headers_mut().set(AccessControlAllowOrigin::Any);
        res.headers_mut().set(AccessControlAllowHeaders(
            vec![UniCase("Content-Type".to_string())]));
        res.version = HttpVersion::Http10;
        let mut res = res.start().unwrap();
        res.write_all(&response).unwrap();
        res.end().unwrap();
    }
}
