#![feature(nll)]

extern crate prusti_launch;

use std::{
    env,
    io::{BufRead, BufReader},
    path::PathBuf,
    process::{Command, Stdio},
};

fn main() {
    if let Err(code) = process(std::env::args().skip(1).collect()) {
        std::process::exit(code);
    }
}

fn process(args: Vec<String>) -> Result<(), i32> {
    let mut prusti_driver_path = std::env::current_exe()
        .expect("current executable path invalid")
        .with_file_name("prusti-driver");
    if cfg!(windows) {
        prusti_driver_path.set_extension("exe");
    }

    let java_home = match env::var("JAVA_HOME") {
        Ok(java_home) => PathBuf::from(java_home),
        Err(_) => prusti_launch::find_java_home()
            .expect("Failed to find Java home directory. Try setting JAVA_HOME"),
    };

    let libjvm_path = prusti_launch::find_libjvm(&java_home)
        .expect("Failed to find JVM library. Check JAVA_HOME");

    let prusti_sysroot = prusti_launch::prusti_sysroot()
        .expect(&format!("Failed to find Rust's sysroot for Prusti"));

    let compiler_lib = prusti_sysroot.join("lib");

    let prusti_home = prusti_driver_path
        .parent()
        .expect("Failed to find Prusti's home");

    let prusti_contracts_lib = prusti_launch::find_prusti_contracts(&prusti_home)
        .expect("Failed to find prusti_contracts library in Prusti's home");

    let mut cmd = Command::new(&prusti_driver_path);
    let has_no_color_arg = args
        .iter()
        .find(|&x| x == "--color" || x.starts_with("--color="))
        .is_none();
    cmd.args(args);
    if has_no_color_arg {
        cmd.args(&["--color", "always"]);
    }
    cmd.env("SYSROOT", &prusti_sysroot);
    cmd.env("PRUSTI_CONTRACTS_LIB", &prusti_contracts_lib);

    let mut libs = vec![compiler_lib, libjvm_path];
    if let Some(target) = option_env!("TARGET") {
        let rustlib_path = prusti_sysroot
            .join("lib")
            .join("rustlib")
            .join(target)
            .join("lib");
        libs.push(rustlib_path);
    }
    prusti_launch::add_to_loader_path(libs, &mut cmd);

    let mut child = cmd
        .stdout(Stdio::piped()) // filter stdout
        .stderr(Stdio::inherit()) // do not filter stderr
        .spawn()
        .expect("could not run prusti-driver");

    // HACK: filter unwanted output
    let stdout = child.stdout.as_mut().expect("failed to open stdout");
    let stdout_reader = BufReader::new(stdout);
    for maybe_line in stdout_reader.lines() {
        let line = maybe_line.expect("failed to read line from stdout");
        if line.starts_with("borrow_live_at is complete") {
            continue;
        }
        if line.starts_with("Could not resolve expression") {
            continue;
        }
        println!("{}", line);
    }

    let exit_status = child.wait().expect("failed to wait for prusti-driver?");

    if exit_status.success() {
        Ok(())
    } else {
        Err(exit_status.code().unwrap_or(-1))
    }
}
