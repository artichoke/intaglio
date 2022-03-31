#![warn(clippy::all)]
#![warn(clippy::pedantic)]
#![warn(clippy::cargo)]
#![allow(unknown_lints)]

#[cfg(feature = "bytes")]
mod bytes;
#[cfg(feature = "cstr")]
mod cstr;
#[cfg(feature = "osstr")]
mod osstr;
#[cfg(feature = "path")]
mod path;
mod str;

#[cfg(not(miri))]
const ITERATIONS: usize = 100_000;
#[cfg(miri)]
const ITERATIONS: usize = 25;
