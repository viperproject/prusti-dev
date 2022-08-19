use std::{process::Command, path::PathBuf};

fn main() {
    // In theory we should build to here (i.e. set `CARGO_TARGET_DIR` to this),
    // but this is hard to find for linking. So instead build to the current dir.
    let _out_dir = std::env::var("OUT_DIR").unwrap();
    // println!("cargo:warning=out_dir: {}", _out_dir);

    // Rebuild if any of the `prusti-contracts` crates change
    println!("cargo:rerun-if-changed=../prusti-contracts");

    // Build `prusti-contracts`
    let dir = if cfg!(debug_assertions) { "debug" } else { "release" };
    // Cargo prusti
    let cp = if cfg!(windows) { "cargo-prusti.exe" } else { "cargo-prusti" };
    let cargo_prusti: PathBuf = ["..", "target", dir, cp].iter().collect();
    println!("cargo:rerun-if-changed={}", cargo_prusti.to_string_lossy());
    // Prusti driver
    let pd = if cfg!(windows) { "prusti-driver.exe" } else { "prusti-driver" };
    let prusti_driver: PathBuf = ["..", "target", dir, pd].iter().collect();
    println!("cargo:rerun-if-changed={}", prusti_driver.to_string_lossy());
    // Run only if possible
    if cargo_prusti.exists() && prusti_driver.exists() {
        let args = ["build", "--release", "--features", "prusti"];
        match Command::new(&cargo_prusti)
            .current_dir("../prusti-contracts")
            .args(&args)
            .output() 
        {
            Ok(output) => {
                if !output.status.success() {
                    let stdout = String::from_utf8(output.stdout).unwrap();
                    let stderr = String::from_utf8(output.stderr).unwrap();
                    println!("cargo:warning=Failed to build `prusti-contracts`!");
                    let args = args.iter().fold(String::new(), |acc, a| acc + " " + a);
                    println!("cargo:warning=`prusti-contracts-build` ran '{}{}'", cargo_prusti.to_string_lossy(), args);
                    println!("cargo:warning=-------- stdout: --------");
                    for line in stdout.lines() {
                        println!("cargo:warning={}", line);
                    }
                    println!("cargo:warning=-------- stderr: --------");
                    for line in stderr.lines() {
                        println!("cargo:warning={}", line);
                    }
                }
            },
            Err(e) => {
                println!("cargo:warning=Failed to build `prusti-contracts`: {}", e);
            }
        }
    } else {

    }
}
