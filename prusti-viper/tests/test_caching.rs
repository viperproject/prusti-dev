// © 2020, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use std::{
    collections::HashMap,
    fs,
    path::{PathBuf, Path},
    process::Command,
};

fn find_executable_path(base_name: &str) -> PathBuf {
    let target_directory = if cfg!(debug_assertions) {
        "debug"
    } else {
        "release"
    };
    let executable_name = if cfg!(windows) {
        format!("{}.exe", base_name)
    } else {
        base_name.to_string()
    };
    let local_prusti_rustc_path: PathBuf = ["target", target_directory, &executable_name]
        .iter()
        .collect();
    if local_prusti_rustc_path.exists() {
        return local_prusti_rustc_path;
    }
    let workspace_prusti_rustc_path: PathBuf = ["..", "target", target_directory, &executable_name]
        .iter()
        .collect();
    if workspace_prusti_rustc_path.exists() {
        return workspace_prusti_rustc_path;
    }
    panic!(
        "Could not find the {:?} prusti-rustc binary to be used in tests. \
        It might be that Prusti has not been compiled correctly.",
        target_directory
    );
}

fn run_on_files<F: FnMut(&Path)>(dir: &Path, run: &mut F) {
    let test_file = dir.join("test_file.rs");
    let mut has_files = false;
    for entry in fs::read_dir(dir).unwrap_or_else(|_| panic!("Did not find dir: {:?}", dir)) {
        let path = entry.unwrap().path();
        std::fs::copy(path, &test_file).unwrap();
        run(&test_file);
        std::fs::remove_file(&test_file).unwrap();
        has_files = true;
    }
    assert!(has_files, "Dir \"{:?}\" did not constain any files!", dir);
}

#[test]
fn test_prusti_rustc_caching() {
    let prusti_rustc = find_executable_path("prusti-rustc");

    let mut hashes: HashMap<String, u64> = HashMap::new();
    let mut run = |program: &Path| {
        println!("Running {:?} on {:?}...", prusti_rustc, program);
        let out = Command::new(&prusti_rustc)
            .arg("--edition=2018")
            .arg("--crate-type=lib")
            .arg("-Pmax_log_file_name_length=120")
            .arg(program)
            .env("RUST_BACKTRACE", "1")
            .env("PRUSTI_DUMP_VIPER_PROGRAM", "true")
            .env("PRUSTI_PRINT_HASH", "true")
            .output()
            .expect("failed to execute prusti-rustc");
        assert!(out.status.success(), "Failed to compile: {:?}\n{}", program, String::from_utf8(out.stderr).unwrap());
        let stdout = String::from_utf8(out.stdout).unwrap();
        let mut hash_lines = stdout.lines()
            .skip_while(|line| !line.starts_with("Received verification request for: "));
        while let Some(l1) = hash_lines.next() {
            let mut full_name = l1.strip_prefix("Received verification request for: ").unwrap().to_string();
            full_name.push_str("-Both.vpr");
            full_name = prusti_common::report::log::to_legal_file_name_of_max_length(full_name, 120);
            let mut name = full_name.split(".rs_");
            let _filename = name.next().unwrap();
            let fn_name = name.next().unwrap();
            let l2 = hash_lines.next().unwrap();
            let hash: u64 = l2.strip_prefix("Hash of the request is: ").unwrap().parse().unwrap();
            std::fs::rename(
                format!("log/viper_program/{}", full_name),
                format!("log/viper_program/{}.vpr", hash)
            ).unwrap();
            hashes.entry(fn_name.to_string())
                .and_modify(|other|
                    if hash != *other {
                        let f1 = std::fs::read_to_string(format!("log/viper_program/{}.vpr", hash)).unwrap();
                        let f2 = std::fs::read_to_string(format!("log/viper_program/{}.vpr", *other)).unwrap();
                        println!("{}", diffy::create_patch(&f1, &f2));
                        std::fs::remove_dir_all("log").unwrap();
                        std::fs::remove_file(program).unwrap();
                        panic!("Hash of function \"{}\" differs: {} vs {}", fn_name, hash, *other);
                    }
                )
                .or_insert(hash);
        }
    };
    run_on_files(&PathBuf::from("tests/hash/"), &mut run);
    std::fs::remove_dir_all("log").unwrap();
}
