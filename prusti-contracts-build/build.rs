use std::{path::PathBuf, process::Command};

fn main() {
    // In theory we should build to here (i.e. set `CARGO_TARGET_DIR` to this),
    // but this is hard to find for linking. So instead build to the `prusti-contracts` dir.
    let _out_dir = std::env::var("OUT_DIR").unwrap();
    // println!("cargo:warning=out_dir: {}", _out_dir);

    // Rebuild if any of the `prusti-contracts` crates change
    let prusti_contrats = ["..", "prusti-contracts"].iter().collect::<PathBuf>();
    let files = std::fs::read_dir(&prusti_contrats).unwrap();
    for file in files {
        let file = file.unwrap();
        let filename = file.file_name();
        let filename = filename.to_string_lossy();
        if filename != "target" {
            println!("cargo:rerun-if-changed={}", file.path().to_string_lossy());
        }
    }

    // Build `prusti-contracts`
    let dir = if cfg!(debug_assertions) {
        "debug"
    } else {
        "release"
    };
    // Cargo prusti
    let exes = ["cargo-prusti", "prusti-rustc", "prusti-driver"].map(|exe| {
        let exe = format!("{}{}", exe, if cfg!(windows) { ".exe" } else { "" });
        let exe = ["..", "target", dir, &exe].iter().collect::<PathBuf>();
        println!("cargo:rerun-if-changed={}", exe.to_string_lossy());
        exe
    });
    // Rerun if running with e.g. cargo clippy
    println!("cargo:rerun-if-env-changed=RUSTC_WORKSPACE_WRAPPER");
    // Run only if possible
    if exes.iter().all(|exe| exe.exists()) {
        let target = prusti_contrats.join("target").join("verify");
        let modified = modified_times(&exes);
        let should_write_build_info =
            check_exes_modified(target.as_path(), &modified).unwrap_or(true);
        let args = ["--release", "--features", "prusti"];
        match Command::new(&exes[0])
            .current_dir(&prusti_contrats)
            .args(args)
            .env("CARGO_PRUSTI_COMMAND", "build")
            .output()
        {
            Ok(output) => {
                if output.status.success() {
                    if should_write_build_info {
                        use std::io::Write;
                        std::fs::File::create(target.join("build_info.txt"))
                            .and_then(|mut file| file.write_all(modified.as_bytes()))
                            .ok();
                    }
                } else {
                    let stdout = String::from_utf8(output.stdout).unwrap();
                    let stderr = String::from_utf8(output.stderr).unwrap();
                    println!("cargo:warning=Failed to build `prusti-contracts`!");
                    let args = args.iter().fold(String::new(), |acc, a| acc + " " + a);
                    println!(
                        "cargo:warning=`prusti-contracts-build` ran '{}{}'",
                        exes[0].to_string_lossy(),
                        args
                    );
                    println!("cargo:warning=-------- stdout: --------");
                    for line in stdout.lines() {
                        println!("cargo:warning={}", line);
                    }
                    println!("cargo:warning=-------- stderr: --------");
                    for line in stderr.lines() {
                        println!("cargo:warning={}", line);
                    }
                    // Only panic when running with `x.py` to avoid errors on the first run
                    if std::env::var("CARGO_FEATURE_PRUSTI_CONTRACTS_DEP").is_ok() {
                        // Delete files to prevent Catch-22 where these files cannot be rebuilt
                        for exe in exes {
                            std::fs::remove_file(exe).ok();
                        }
                        panic!("Fix the above Prusti crash and run build again to rebuild Prusti.")
                    } else {
                        std::fs::remove_dir_all(target).ok();
                    }
                }
            }
            Err(e) => {
                println!("cargo:warning=Failed to build `prusti-contracts`: {}", e);
            }
        }
    } else {
    }
}

/// Cargo will rebuild prusti-contracts if any of those files changed, however we want to
/// rebuild them also if any of the `cargo-prusti`/`prusti-{rustc,driver}` changed, and so
/// we manually force that here if required.
fn check_exes_modified(target: &std::path::Path, modified: &str) -> std::io::Result<bool> {
    let contents = std::fs::read_to_string(target.join("build_info.txt"))?;
    if contents != modified {
        let files = std::fs::read_dir(target.join("release").join("deps"))?;
        let libs = prusti_launch::PRUSTI_LIBS.map(|lib| format!("lib{}-", lib.replace('-', "_")));
        for file in files {
            let file = file.unwrap();
            let filename = file.file_name();
            let filename = filename.to_string_lossy();
            if libs.iter().any(|lib| filename.starts_with(lib)) {
                std::fs::remove_file(file.path()).ok();
            }
        }
        Ok(true)
    } else {
        Ok(false)
    }
}

fn modified_times(files: &[PathBuf]) -> String {
    files
        .iter()
        .map(|f| {
            f.metadata()
                .unwrap()
                .modified()
                .unwrap()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_millis()
                .to_string()
        })
        .collect::<Vec<_>>()
        .join("\n")
}
