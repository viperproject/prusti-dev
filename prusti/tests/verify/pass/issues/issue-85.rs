//! Source: crate crossbeam-channel

extern crate prusti_contracts;

use std::thread;
use std::time::Duration;

/// Blocks the current thread forever.
fn sleep_forever() -> ! {
    loop {
        thread::sleep(Duration::from_secs(1000));
    }
}

fn main(){}
