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

#[allow(dead_code)]
mod vectors {
    use core::iter;

    #[cfg(not(miri))]
    const ITERATIONS: usize = 100_000;
    #[cfg(miri)]
    const ITERATIONS: usize = 25;

    pub fn symbols() -> impl Iterator<Item = String> {
        ('\0'..'\x7F')
            .cycle()
            .enumerate()
            .take(ITERATIONS)
            .map(|(i, ch)| {
                let len = (i / 256) + 100;
                iter::repeat(ch).take(len).collect::<String>()
            })
    }

    pub fn byte_symbols() -> impl Iterator<Item = Vec<u8>> {
        (b'\x00'..=b'\xFF')
            .cycle()
            .enumerate()
            .take(ITERATIONS)
            .map(|(i, ch)| {
                let len = (i / 256) + 100;
                iter::repeat(ch).take(len).collect::<Vec<_>>()
            })
    }

    pub fn byte_symbols_no_nul() -> impl Iterator<Item = Vec<u8>> {
        (b'\x01'..=b'\xFF')
            .cycle()
            .enumerate()
            .take(ITERATIONS)
            .map(|(i, ch)| {
                let len = (i / 256) + 100;
                iter::repeat(ch).take(len).collect::<Vec<_>>()
            })
    }
}
