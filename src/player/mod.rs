mod random_player;
mod legal_player;
mod comp_delib_player;
mod minimax_player;
mod alpha_beta_player;
mod mcs_player;

pub use self::random_player::RandomPlayer;
pub use self::legal_player::LegalPlayer;
pub use self::comp_delib_player::CompDelibPlayer;
pub use self::minimax_player::MinimaxPlayer;
pub use self::alpha_beta_player::AlphaBetaPlayer;
pub use self::mcs_player::McsPlayer;
