#![warn(clippy::all)]
#![warn(clippy::pedantic)]
#![warn(clippy::cargo)]
#![allow(unknown_lints)]

use core::iter;

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

fn symbols() -> impl Iterator<Item = String> {
    ('\0'..'\x7F')
        .cycle()
        .enumerate()
        .take(ITERATIONS)
        .map(|(i, ch)| {
            let len = (i / 256) + 100;
            iter::repeat(ch).take(len).collect::<String>()
        })
}

fn byte_symbols() -> impl Iterator<Item = Vec<u8>> {
    (b'\x00'..=b'\xFF')
        .cycle()
        .enumerate()
        .take(ITERATIONS)
        .map(|(i, ch)| {
            let len = (i / 256) + 100;
            iter::repeat(ch).take(len).collect::<Vec<_>>()
        })
}

fn byte_symbols_no_nul() -> impl Iterator<Item = Vec<u8>> {
    (b'\x01'..=b'\xFF')
        .cycle()
        .enumerate()
        .take(ITERATIONS)
        .map(|(i, ch)| {
            let len = (i / 256) + 100;
            iter::repeat(ch).take(len).collect::<Vec<_>>()
        })
}
