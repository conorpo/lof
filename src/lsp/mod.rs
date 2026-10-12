//! A small stdio language server sharing the real LOF frontend and kernel.

mod protocol;
mod server;
mod text;

pub use server::run;

#[cfg(test)]
mod tests;
