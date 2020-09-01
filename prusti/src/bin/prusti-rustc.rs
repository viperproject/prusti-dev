use prusti_launch::{add_to_loader_path, prusti_sysroot};
use std::{
    env,
    path::PathBuf,
    process::{Command, Stdio},
};

fn process(mut args: Vec<String>) -> Result<(), i32> {
    let mut prusti_driver_path = env::current_exe()
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

    let prusti_sysroot =
        prusti_sysroot().expect(&format!("Failed to find Rust's sysroot for Prusti"));

    let compiler_lib = prusti_sysroot.join("lib");

    let prusti_home = prusti_driver_path
        .parent()
        .expect("Failed to find Prusti's home");

    let mut cmd = Command::new(&prusti_driver_path);

    if let Some(target) = option_env!("TARGET") {
        let rustlib_path = prusti_sysroot
            .join("lib")
            .join("rustlib")
            .join(target)
            .join("lib");
        add_to_loader_path(vec![rustlib_path, compiler_lib, libjvm_path], &mut cmd);
    } else {
        add_to_loader_path(vec![compiler_lib, libjvm_path], &mut cmd);
    }

    let has_no_color_arg = args
        .iter()
        .find(|&x| x == "--color" || x.starts_with("--color="))
        .is_none();
    if has_no_color_arg {
        cmd.args(&["--color", "always"]);
    }

    if !args.iter().any(|s| s == "--sysroot") {
        args.push("--sysroot".to_string());
        args.push(
            prusti_sysroot
                .into_os_string()
                .into_string()
                .expect("sysroot is not a valid utf-8 string"),
        );
    };

    cmd.args(args);

    cmd.arg("-L");
    cmd.arg(format!(
        "dependency={}",
        prusti_home
            .as_os_str()
            .to_str()
            .expect("the Prusti HOME path contains invalid UTF-8")
    ));

    cmd.arg("--extern");
    let prusti_contracts_path = prusti_home.join("libprusti_contracts.rlib");
    cmd.arg(format!(
        "prusti_contracts={}",
        prusti_contracts_path
            .as_os_str()
            .to_str()
            .expect("the Prusti contracts path contains invalid UTF-8")
    ));

    let dylib_extension = if cfg!(target_os = "macos") {
        "dylib"
    } else {
        "so"
    };
    let prusti_internal_path =
        prusti_home.join(format!("libprusti_contracts_internal.{}", dylib_extension));
    cmd.arg("--extern");
    cmd.arg(format!(
        "prusti_contracts_internal={}",
        prusti_internal_path
            .as_os_str()
            .to_str()
            .expect("the internal Prusti contracts path contains invalid UTF-8")
    ));

    // cmd.arg("-Zreport-delayed-bugs");
    // cmd.arg("-Ztreat-err-as-bug=1");

    let mut child = cmd
        .stdout(Stdio::piped()) // filter stdout (see below)
        .stderr(Stdio::inherit()) // do not filter stderr
        .spawn()
        .expect("could not run prusti-driver");

    // HACK: filter unwanted output
    let stdout = child.stdout.as_mut().expect("failed to open stdout");
    let stdout_reader = BufReader::new(stdout);
    for maybe_line in stdout_reader.lines() {
        let line = maybe_line.expect("failed to read line from stdout");
        // Filter an annoying Viper message
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

fn main() {
    if let Err(code) = process(std::env::args().skip(1).collect()) {
        std::process::exit(code);
    }
}
