#![feature(std_misc, plugin)]
#![plugin(regex_macros)]

extern crate gdl_parser;
extern crate hyper;
extern crate regex;

#[macro_use]
extern crate log;

mod game_manager;
mod gdl;
mod prover;

use hyper::Server;
use hyper::server::{Request, Response, Handler};
use hyper::net::Fresh;

use std::net::ToSocketAddrs;
use std::io::Read;
use std::io::Write;
use std::ascii::OwnedAsciiExt;
use std::sync::Mutex;

use game_manager::GameManager;

pub use game_manager::Game;
pub use gdl::Move;

pub trait Player {
    fn get_name(&self) -> String;

    fn meta_game(&self, game: &Game) {}

    fn select_move(&self, game: &Game) -> Move;

    fn stop(&self, game: &Game) {}
}

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
    fn handle(&self, mut req: Request, res: Response<Fresh>) {
        let mut res = res.start().unwrap();
        let mut s = String::new();
        req.read_to_string(&mut s).unwrap();
        let s = s.into_ascii_lowercase();
        debug!("Got request: {}", s);

        let mut gm = self.gm.lock().unwrap();
        let s = gm.handle(s);
        res.write_all(&s.into_bytes()).unwrap();
        res.end().unwrap();
    }
}
