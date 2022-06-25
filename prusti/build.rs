use chrono::{prelude::Utc, DateTime, NaiveDateTime};
use std::process::Command;

fn main() {
    println!(
        "cargo:rustc-env=TARGET={}",
        std::env::var("TARGET").unwrap()
    );

    if let Some(commit_hash) = Command::new("git")
        .args(&["rev-parse", "--short", "HEAD"])
        .output()
        .ok()
        .and_then(|output| String::from_utf8(output.stdout).ok())
    {
        println!("cargo:rustc-env=COMMIT_HASH={}", commit_hash);
    }

    if let Some(commit_timestamp) = Command::new("git")
        .args(&["show", "-s", "--format=%ct"])
        .output()
        .ok()
        .and_then(|output| String::from_utf8(output.stdout).ok())
    {
        if let Ok(timestamp) = commit_timestamp.trim().parse() {
            let commit_naive_datetime = NaiveDateTime::from_timestamp(timestamp, 0);
            let commit_time = DateTime::<Utc>::from_utc(commit_naive_datetime, Utc);
            println!(
                "cargo:rustc-env=COMMIT_TIME={}",
                commit_time.format("%F %T %Z")
            );
        }
    }

    println!(
        "cargo:rustc-env=BUILD_TIME={}",
        Utc::now().format("%F %T %Z")
    );
}
