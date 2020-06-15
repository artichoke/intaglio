#![allow(dead_code)]

#[cfg(target_os = "linux")]
use std::mem::MaybeUninit;

#[derive(Debug)]
pub struct Looper<'a, T> {
    test: &'a str,
    subject: T,
    iterations: usize,
    tolerance: i64, // in bytes
}

impl<'a, T> Looper<'a, T> {
    pub fn new(test: &'a str, subject: T) -> Self {
        Self {
            test,
            subject,
            iterations: 0,
            tolerance: 0,
        }
    }

    pub fn with_iterations(mut self, iterations: usize) -> Self {
        self.iterations = iterations;
        self
    }

    pub fn with_tolerance(mut self, tolerance: i64) -> Self {
        self.tolerance = tolerance;
        self
    }

    pub fn check_leaks<F>(self, execute: F)
    where
        F: FnMut(usize, &mut T),
    {
        self.check_leaks_with_finalizer(execute, |_| {});
    }

    pub fn check_leaks_with_finalizer<F, G>(mut self, mut execute: F, finalize: G)
    where
        F: FnMut(usize, &mut T),
        G: FnOnce(T),
    {
        let start_mem = resident_memsize();
        for i in 0..self.iterations {
            execute(i, &mut self.subject);
        }
        finalize(self.subject);
        let end_mem = resident_memsize();
        assert!(
            end_mem <= start_mem + self.tolerance,
            "Plausible memory leak in test {}!\nAfter {} iterations, usage before: {}, usage after: {}",
            self.test,
            self.iterations,
            start_mem,
            end_mem
        );
    }
}

#[cfg(target_os = "linux")]
#[allow(clippy::identity_conversion)]
fn resident_memsize() -> i64 {
    let mut out = MaybeUninit::<libc::rusage>::uninit();
    assert!(unsafe { libc::getrusage(libc::RUSAGE_SELF, out.as_mut_ptr()) } == 0);
    let out = unsafe { out.assume_init() };
    out.ru_maxrss.into()
}

#[cfg(not(target_os = "linux"))]
fn resident_memsize() -> i64 {
    0
}
