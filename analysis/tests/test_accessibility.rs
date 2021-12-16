mod utils;

use glob::glob;
use std::{
    env,
    ffi::OsStr,
    fmt, fs,
    path::{Path, PathBuf},
    process::{Command, Stdio},
};
use utils::*;

/// Prepend paths to an environment variable
fn env_prepend_path(name: &str, value: Vec<PathBuf>, cmd: &mut Command) {
    let old_value = env::var_os(name);
    let mut parts = value;
    if let Some(ref v) = old_value {
        parts.extend(env::split_paths(v).collect::<Vec<_>>());
    };
    match env::join_paths(parts) {
        Ok(new_value) => {
            cmd.env(name, new_value);
        }
        Err(err) => panic!("Error: {:?}", err),
    }
}

/// Append paths to the loader environment variable
fn add_to_loader_path(paths: Vec<PathBuf>, cmd: &mut Command) {
    #[cfg(target_os = "windows")]
    const LOADER_PATH: &str = "PATH";
    #[cfg(target_os = "linux")]
    const LOADER_PATH: &str = "LD_LIBRARY_PATH";
    #[cfg(target_os = "macos")]
    const LOADER_PATH: &str = "DYLD_FALLBACK_LIBRARY_PATH";
    env_prepend_path(LOADER_PATH, paths, cmd);
}

fn generate_program_testing_accessible_paths(
    program_path: impl AsRef<OsStr> + fmt::Debug,
) -> Vec<String> {
    let compiler_sysroot = PathBuf::from(find_sysroot());
    let compiler_bin = compiler_sysroot.join("bin");
    let compiler_lib = compiler_sysroot.join("lib");
    let executable_path = find_compiled_executable("gen-accessibility-driver");

    let mut cmd = Command::new(executable_path);
    cmd.args(["--edition=2018", "--crate-type=lib", "--sysroot"])
        .arg(
            compiler_sysroot
                .into_os_string()
                .into_string()
                .expect("sysroot is not a valid utf-8 string"),
        )
        .arg("--generate-test-program")
        .arg(&program_path);

    add_to_loader_path(vec![compiler_lib, compiler_bin], &mut cmd);

    println!("Running {:?}", cmd);
    let output = cmd
        .env("RUST_BACKTRACE", "1")
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .output()
        .unwrap_or_else(|err| panic!("Failed to execute process: {:?}", err));

    let stdout = String::from_utf8_lossy(&output.stdout);
    if !output.status.success() {
        println!("Test case {:?} unexpectedly failed.", program_path);
        println!("Exit status: {:?}", output.status);
        println!("┌─── Begin of stdout ───┐");
        println!("{}", stdout);
        println!("└──── End of stdout ────┘");
        println!("┌─── Begin of stderr ───┐");
        println!("{}", String::from_utf8_lossy(&output.stderr));
        println!("└──── End of stderr ────┘");
        panic!("Test case unexpectedly failed. See the output for details.");
    }

    stdout
        .to_string()
        .split("\n/* NEW PROGRAM */\n\n")
        .map(|s| s.to_string())
        .collect()
}

fn check_compile_pass(cwd: impl AsRef<Path>, program_path: impl AsRef<OsStr> + fmt::Debug) {
    let mut cmd = Command::new("rustc");
    cmd.args(["--edition=2018", "--crate-type=lib", "-Zpolonius"])
        .arg(&program_path);
    println!("Running {:?}", cmd);
    let output = cmd
        .current_dir(cwd)
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .output()
        .unwrap_or_else(|err| panic!("Failed to execute process: {:?}", err));
    if !output.status.success() {
        println!("Program {:?} failed to compile.", &program_path);
        println!("Exit status: {:?}", output.status);
        println!("┌─── Begin of stdout ───┐");
        println!("{}", String::from_utf8_lossy(&output.stdout));
        println!("└──── End of stdout ────┘");
        println!("┌─── Begin of stderr ───┐");
        println!("{}", String::from_utf8_lossy(&output.stderr));
        println!("└──── End of stderr ────┘");
        panic!("Test case unexpectedly failed. See the output for details.");
    }
}

/// Collect test programs composed of just one file.
fn collect_standalone_test_programs() -> Vec<PathBuf> {
    let mut programs = vec![];
    let glob_paths = [
        "tests/test_cases/gen_accessibility/*.rs",
        "tests/test_cases/gen_accessibility/**/*.rs",
        //"../prusti-tests/tests/verify*/fail/no-annotations/*.rs",
        //"../prusti-tests/tests/verify*/pass/no-annotations/*.rs",
    ];
    for glob_path in &glob_paths {
        let mut new_programs: Vec<_> = glob(glob_path)
            .unwrap()
            .map(|result| result.unwrap())
            .collect();
        println!(
            "Collected {} test programs from {:?}",
            new_programs.len(),
            glob_path
        );
        assert!(!new_programs.is_empty());
        new_programs.sort();
        programs.append(&mut new_programs);
    }
    assert!(programs.len() >= glob_paths.len());
    programs
}

/// Test the correctness of the analysis by injecting `let _ = & <place>` (respectively,
/// `let _ = &mut <place>`) statements wherever the `DefinitelyAccessibleAnalysis` believes that
/// a place is accessible by read (respectively, write) operations.
#[test]
fn test_accessibility() {
    let test_programs = collect_standalone_test_programs();
    println!("Collected {} test programs", test_programs.len());
    let out_dir = env::temp_dir().join("prusti_test_analysis");
    if out_dir.exists() {
        fs::remove_dir_all(&out_dir).expect("Failed to remove output directory");
    }
    fs::create_dir(&out_dir).expect("Failed to create output directory");
    println!("Output directory: {:?}", out_dir);

    for (test_num, test_program) in test_programs.iter().enumerate() {
        println!(
            "Testing on {:?} ({}/{})",
            test_program,
            test_num,
            test_programs.len()
        );
        let gen_programs = generate_program_testing_accessible_paths(test_program);
        assert!(gen_programs.len() > 0);
        println!("The analysis generated {} programs", gen_programs.len());
        let limit = 10;
        if gen_programs.len() > limit {
            println!(
                "Too many generated programs. Only the first {} will be considered.",
                limit
            );
        }
        for (gen_num, gen_program) in gen_programs.iter().take(limit).enumerate() {
            let test_filename = test_program.file_name().unwrap().to_str().unwrap();
            let gen_path =
                out_dir.join(format!("{:03}_{:02}_{}", test_num, gen_num, test_filename));
            println!(
                "Generated program: {:?} ({}/{})",
                gen_path,
                gen_num,
                gen_programs.len()
            );
            println!("┌─── Begin of generated program ───┐");
            println!("{}", gen_program);
            println!("└──── End of generated program ────┘");

            // Check that it compiles successfully
            std::fs::write(&gen_path, gen_program).unwrap();
            check_compile_pass(&out_dir, gen_path);
        }
    }

    println!("All tests passed. Removing output directory {:?}", out_dir);
    // Note that this does *not* remove the output directory in case of failures.
    // It's done on purpose to help debugging.
    fs::remove_dir_all(&out_dir).expect("Failed to remove output directory");
}
