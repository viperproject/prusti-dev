// © 2020, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use std::path::Path;
use std::error::Error;
use std::io::Read;
use std::fs::File;
use std::fmt;

use rustwide::{cmd::SandboxBuilder, Crate, Toolchain, WorkspaceBuilder};
use serde::Deserialize;
use log::{info, error};

#[derive(Debug, Deserialize)]
struct CrateRecord {
    name: String,
    version: String,
}

impl fmt::Display for CrateRecord {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} {}", self.name, self.version)
    }
}

fn setup_logs() {
    let mut env = env_logger::Builder::new();
    env.filter_module("test_crates", log::LevelFilter::Info);
    if let Ok(content) = std::env::var("TEST_CRATES_LOG") {
        env.parse_filters(&content);
    }
    rustwide::logging::init_with(env.build());
}

fn main() -> Result<(), Box<dyn Error>> {
    color_backtrace::install();
    setup_logs();

    info!("Crate a new workspace...");
    let workspace = WorkspaceBuilder::new(
        Path::new("../workspaces/test-crates-builder"),
        "prusti-test-crates"
    ).init()?;

    info!("Install the toolchain...");
    let toolchain = {
        let mut contents = String::new();
        std::fs::File::open("rust-toolchain")
            .expect("Failed to open file 'rust-toolchain'.")
            .read_to_string(&mut contents)
            .expect("Failed to read file 'rust-toolchain'.");
        let dist = contents.trim().to_string();
        info!("toolchain: {}", dist);
        Toolchain::dist(&dist)
    };
    //toolchain.add_component(&workspace, "rustc-dev")?;
    toolchain.install(&workspace)?;

    info!("Read list of crates...");
    let crate_list_file = File::open("test-crates/crates.csv")?;
    let mut crate_list_reader = csv::Reader::from_reader(crate_list_file);

    info!("Iterate over all crates in the list...");
    for result in crate_list_reader.deserialize() {
        let crate_record: CrateRecord = result?;
        info!("Crate: {}", crate_record);

        info!("Fetch crate...");
        let krate = Crate::crates_io(&crate_record.name, &crate_record.version);
        krate.fetch(&workspace)?;

        info!("Configure sandbox...");
        let sandbox = SandboxBuilder::new()
            .memory_limit(Some(1024 * 1024 * 1024))
            .enable_networking(false);

        info!("Build crate...");
        let mut crate_build_dir = workspace.build_dir(
            &format!("build_{}_{}", &crate_record.name, &crate_record.version)
        );
        let build_result = crate_build_dir.build(&toolchain, &krate, sandbox).run(|build| {
            build.cargo().args(&["check"]).run()?;
            Ok(())
        });
        if let Err(build_error) = build_result {
            error!("Error: {}", build_error);
        }
    }

    Ok(())
}
