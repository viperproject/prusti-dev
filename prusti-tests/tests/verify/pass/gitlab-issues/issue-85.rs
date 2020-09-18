//! Source: crate crossbeam-channel

use prusti_contracts::*;

use std::thread;
use std::time::Duration;

/// Blocks the current thread forever.
fn sleep_forever() -> ! {
    loop {
        let x = 1000;
        thread::sleep(Duration::from_secs(x));
    }
}

fn main(){}
