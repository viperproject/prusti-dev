// © 2020, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use std::{
    env,
    error::Error,
    fs,
    path::{Path, PathBuf},
    process::Command,
};
use log::{error, info, warn, LevelFilter};
use rustwide::{cmd, logging, logging::LogStorage, Crate, Toolchain, Workspace, WorkspaceBuilder};
use serde::Deserialize;
use clap::Parser;

/// How a crate should be tested. All tests use `check_panics=false`, `check_overflows=false` and
/// `skip_unsupported_features=true`.
#[derive(Clone, Copy, Debug, Deserialize, PartialEq, Eq)]
enum TestKind {
    /// Test that Prusti does not crash nor generate "internal/invalid" when the
    /// `allow_unreachable_unsupported_code` flag is set.
    NoErrorsWithUnreachableUnsupportedCode,
    /// Test that Prusti does not crash nor generate "internal/invalid" errors.
    NoErrors,
    /// Test that Prusti does not crash nor generate "invalid" errors.
    NoCrash,
    /// Skip the crate. Prusti crashes or the crate does not compile with the standard compiler.
    Skip,
}

#[derive(Debug, Deserialize)]
struct CrateRecord {
    name: String,
    version: String,
    test_kind: TestKind,
}

fn setup_logs() {
    let mut env = env_logger::Builder::new();
    env.filter_module("test_crates", log::LevelFilter::Info);
    if let Ok(content) = std::env::var("TEST_CRATES_LOG") {
        env.parse_filters(&content);
    }
    rustwide::logging::init_with(env.build());
}

struct CargoPrusti {
    prusti_home: PathBuf,
    viper_home: PathBuf,
    z3_exe: PathBuf,
    java_home: Option<PathBuf>,
}

impl cmd::Runnable for CargoPrusti {
    fn name(&self) -> cmd::Binary {
        cmd::Binary::Global(self.prusti_home.join("cargo-prusti"))
    }

    fn prepare_command<'w, 'pl>(&self, cmd: cmd::Command<'w, 'pl>) -> cmd::Command<'w, 'pl> {
        let java_home = self
            .java_home
            .as_ref()
            .map(|p| p.to_str().unwrap())
            .unwrap_or("/usr/lib/jvm/default-java");
        cmd.env("VIPER_HOME", self.viper_home.to_str().unwrap())
            .env("Z3_EXE", self.z3_exe.join("z3").to_str().unwrap())
            .env("JAVA_HOME", java_home)
            .env("PRUSTI_CARGO_PATH", "/opt/rustwide/cargo-home/bin/cargo")
    }
}

#[derive(Deserialize)]
struct RustToolchainFile {
    toolchain: RustToolchain,
}

#[derive(Deserialize)]
struct RustToolchain {
    channel: String,
    components: Option<Vec<String>>,
}

fn get_rust_toolchain() -> RustToolchain {
    let content = include_str!("../../rust-toolchain");
    let rust_toolchain: RustToolchainFile =
        toml::from_str(content).expect("failed to parse rust-toolchain file");
    rust_toolchain.toolchain
}

/// Find the Java home directory
pub fn find_java_home() -> Option<PathBuf> {
    Command::new("java")
        .arg("-XshowSettings:properties")
        .arg("-version")
        .output()
        .ok()
        .and_then(|output| {
            let stdout = String::from_utf8_lossy(&output.stdout);
            let stderr = String::from_utf8_lossy(&output.stderr);
            for line in stdout.lines().chain(stderr.lines()) {
                if line.contains("java.home") {
                    let pos = line.find('=').unwrap() + 1;
                    let path = line[pos..].trim();
                    return Some(PathBuf::from(path));
                }
            }
            None
        })
}

/// Collect the directories containing java policy files.
pub fn collect_java_policies() -> Vec<PathBuf> {
    glob::glob("/etc/java-*")
        .unwrap()
        .map(|result| result.unwrap())
        .collect()
}

/// A tool to test Prusti on a variety of public crates.
#[derive(Parser, Debug)]
#[clap(version, about, long_about = None)]
struct Args {
    /// Do not check whether the crates compile successfully without Prusti.
    #[clap(long)]
    skip_build_check: bool,

    /// If specified, only test crates containing this string in their names.
    #[clap(value_name = "CRATENAME", default_value_t = String::from(""))]
    filter_crate_name: String,

    /// If true, the process will terminate at the first failing crate instead of waiting until all
    /// crates are tested.
    #[clap(long)]
    fail_fast: bool,

    /// Number of shards into which to split the list of crates. Only one of them will be tested.
    #[clap(long, value_parser, default_value_t = 1)]
    num_shards: usize,

    /// The index of the shard of crates that should be tested, in the range [0, num_shards).
    #[clap(long, value_parser, default_value_t = 0)]
    shard_index: usize,
}

fn attempt_fetch(krate: &Crate, workspace: &Workspace, num_retries: u8) -> Result<(), failure::Error> {
    let mut i = 0;
    while i < num_retries + 1 {
        if let Err(err) = krate.fetch(workspace) {
            warn!("Error fetching crate {}: {}", krate, err);
            if i == num_retries {
                // Last attempt failed, return the error
                return Err(err)
            }
        } else {
            return Ok(())
        }
        i += 1;
    }
    unreachable!()
}

fn main() -> Result<(), Box<dyn Error>> {
    color_backtrace::install();
    setup_logs();

    let args = Args::parse();

    // Check consistency of the arguments
    assert!(
        args.shard_index < args.num_shards,
        "The shard index ({}) must be less than the number of shards ({})",
        args.shard_index,
        args.num_shards,
    );

    let workspace_path = Path::new("../workspaces/test-crates-builder");
    let host_prusti_home = if cfg!(debug_assertions) {
        Path::new("target/debug")
    } else {
        Path::new("target/release")
    };
    let host_viper_home = Path::new("viper_tools/backends");
    let host_z3_home = Path::new("viper_tools/z3/bin");
    let host_java_home = env::var("JAVA_HOME")
        .ok()
        .map(|s| s.into())
        .or_else(find_java_home)
        .expect("Please set JAVA_HOME");
    let host_java_policies = collect_java_policies();
    let guest_prusti_home = Path::new("/opt/rustwide/prusti-home");
    let guest_viper_home = Path::new("/opt/rustwide/viper-home");
    let guest_z3_home = Path::new("/opt/rustwide/z3-home");
    // Map JAVA at exactly the same location on the guest so that symlinks work.
    let guest_java_home = host_java_home.clone();

    info!("Using host's Java home {:?}", host_java_home);
    let cargo_prusti = CargoPrusti {
        prusti_home: guest_prusti_home.to_path_buf(),
        viper_home: guest_viper_home.to_path_buf(),
        z3_exe: guest_z3_home.to_path_buf(),
        java_home: Some(guest_java_home.clone()),
    };

    info!("Create a new workspace...");
    // `Error: Compat { error: SandboxImagePullFailed(ExecutionFailed(ExitStatus(unix_wait_status(256)))) }` if
    // docker daemon isn't running
    let workspace = WorkspaceBuilder::new(workspace_path, "prusti-test-crates").init()?;

    info!("Install the toolchain...");
    let rust_toolchain = get_rust_toolchain();
    info!("toolchain: {}", rust_toolchain.channel);
    let toolchain = Toolchain::dist(&rust_toolchain.channel);
    toolchain.install(&workspace)?;
    for component in rust_toolchain.components.as_ref().unwrap_or(&vec![]).iter() {
        if component != "rustfmt" {
            toolchain.add_component(&workspace, component)?;
        }
    }

    info!("Read lists of crates...");
    // TODO: Use the appropriate file from `cargo-locks/` to freeze the version of the dependencies.
    let crates_list: Vec<(Crate, TestKind)> =
        csv::Reader::from_reader(fs::File::open("test-crates/crates.csv")?)
            .deserialize()
            .collect::<Result<Vec<CrateRecord>, _>>()?
            .into_iter()
            .filter(|record| record.name.contains(&args.filter_crate_name))
            .map(|record| (Crate::crates_io(&record.name, &record.version), record.test_kind))
            .collect();
    info!("There are {} crates in total.", crates_list.len());

    // List of crates that don't compile with the standard compiler.
    let mut skipped_crates = vec![];
    // List of crates on which Prusti fails.
    let mut failed_crates = vec![];
    // List of crates on which Prusti succeed.
    let mut successful_crates = vec![];

    let shard_crates_list: Vec<&(Crate, TestKind)> = crates_list.iter().skip(args.shard_index)
        .step_by(args.num_shards).collect();
    info!(
        "Iterate over the {} crates of the shard {}/{}...",
        shard_crates_list.len(),
        args.shard_index,
        args.num_shards,
    );
    for (index, (krate, test_kind)) in shard_crates_list.iter().enumerate() {
        info!("Crate {}/{}: {}, test kind: {:?}", index, shard_crates_list.len(), krate, test_kind);

        if let TestKind::Skip = test_kind {
            info!("Skip crate");
            // Do not try to verify this crate
            skipped_crates.push((krate, test_kind));
            continue;
        }

        info!("Fetch crate...");
        attempt_fetch(krate, &workspace, 2)?;

        if !args.skip_build_check {
            info!("Build crate...");
            let mut build_dir = workspace.build_dir(&format!("build_{index}"));

            let sandbox = cmd::SandboxBuilder::new()
                .memory_limit(Some(1024 * 1024 * 1024))
                .enable_networking(false);

            let mut storage = LogStorage::new(LevelFilter::Info);
            storage.set_max_size(1024 * 1024);

            let build_status = build_dir.build(&toolchain, krate, sandbox).run(|build| {
                logging::capture(&storage, || {
                    build.cargo().args(&["check"]).run()?;
                    Ok(())
                })
            });

            if let Err(err) = build_status {
                warn!("Error: {:?}", err);
                warn!("Output:\n{}", storage);

                // Report the failure
                failed_crates.push((krate, test_kind));
                continue;
            }
        }

        info!("Verify crate...");
        {
            let mut build_dir = workspace.build_dir(&format!("verify_{index}"));

            let mut sandbox = cmd::SandboxBuilder::new()
                .memory_limit(Some(4024 * 1024 * 1024))
                .enable_networking(false)
                .mount(
                    host_prusti_home,
                    guest_prusti_home,
                    cmd::MountKind::ReadOnly,
                )
                .mount(
                    host_viper_home,
                    guest_viper_home,
                    cmd::MountKind::ReadOnly,
                )
                .mount(host_z3_home, guest_z3_home, cmd::MountKind::ReadOnly)
                .mount(&host_java_home, &guest_java_home, cmd::MountKind::ReadOnly);
            for java_policy_path in &host_java_policies {
                sandbox =
                    sandbox.mount(java_policy_path, java_policy_path, cmd::MountKind::ReadOnly);
            }

            let mut storage = LogStorage::new(LevelFilter::Info);
            storage.set_max_size(1024 * 1024);

            let verification_status = build_dir.build(&toolchain, krate, sandbox).run(|build| {
                logging::capture(&storage, || {
                    let mut command = build.cmd(&cargo_prusti)
                        .env("RUST_BACKTRACE", "1")
                        .env("PRUSTI_ASSERT_TIMEOUT", "60000")
                        .env("PRUSTI_LOG_DIR", "/tmp/prusti_log")
                        .env("PRUSTI_CHECK_PANICS", "false")
                        .env("PRUSTI_CHECK_OVERFLOWS", "false")
                        // Do not report errors for unsupported language features
                        .env("PRUSTI_SKIP_UNSUPPORTED_FEATURES", "true");
                    match test_kind {
                        TestKind::NoErrorsWithUnreachableUnsupportedCode => {
                            command = command.env("PRUSTI_ALLOW_UNREACHABLE_UNSUPPORTED_CODE", "true");
                        }
                        TestKind::NoErrors => {},
                        TestKind::NoCrash => {
                            // Report internal errors as warnings
                            command = command.env("PRUSTI_INTERNAL_ERRORS_AS_WARNINGS", "true");
                        },
                        TestKind::Skip => {
                            unreachable!();
                        }
                    }
                    command.run()?;
                    Ok(())
                })
            });

            if let Err(err) = verification_status {
                error!("Error: {:?}", err);
                error!("Output:\n{}", storage);

                // Report the failure
                failed_crates.push((krate, test_kind));
            } else {
                successful_crates.push((krate, test_kind));
            }
        }

        if args.fail_fast {
            if let Some((krate, test_kind)) = failed_crates.first() {
                panic!("Failed to verify the crate {krate} ({test_kind:?})");
            }
        }
    }

    // Report summary
    if !successful_crates.is_empty() {
        info!("Successfully verified {} crates:", successful_crates.len());
        for (krate, test_kind) in &successful_crates {
            info!(" - {} ({:?})", krate, test_kind);
        }
    }
    if !skipped_crates.is_empty() {
        warn!("Skipped {} crates:", skipped_crates.len());
        for (krate, test_kind) in &skipped_crates {
            warn!(" - {} ({:?})", krate, test_kind);
        }
    }
    if !failed_crates.is_empty() {
        error!("Failed to verify {} crates:", failed_crates.len());
        for (krate, test_kind) in &failed_crates {
            error!(" - {} ({:?})", krate, test_kind);
        }
    }

    // Panic
    assert!(failed_crates.is_empty(), "Failed to verify {} crates", failed_crates.len());

    Ok(())
}
