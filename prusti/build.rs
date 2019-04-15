extern crate chrono;

use std::process::Command;
use chrono::prelude::Utc;

fn main() {
    let output = Command::new("git").args(&["rev-parse", "--short", "HEAD"]).output()
        .expect("Failed to obtain git hash");
    let git_hash = String::from_utf8(output.stdout)
        .expect("Failed to parse git hash");
    println!("cargo:rustc-env=GIT_HASH={}", git_hash);

    let build_time = Utc::now().format("%Y-%m-%d %H:%M:%S").to_string();
    println!("cargo:rustc-env=BUILD_TIME={}", build_time);
}
