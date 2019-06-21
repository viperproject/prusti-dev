extern crate chrono;

use chrono::prelude::Utc;
use std::process::Command;

fn main() {
    if let Some(git_hash) = Command::new("git")
        .args(&["rev-parse", "--short=19", "HEAD"])
        .output()
        .ok()
        .and_then(|output| String::from_utf8(output.stdout).ok())
    {
        println!("cargo:rustc-env=GIT_HASH={}", git_hash);
    }

    let build_time = Utc::now().format("%Y-%m-%d %H:%M:%S").to_string();
    println!("cargo:rustc-env=BUILD_TIME={}", build_time);
}
