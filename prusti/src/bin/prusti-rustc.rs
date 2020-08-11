use prusti_env_utils::{add_to_loader_path, get_latest_crate_artefact, prusti_sysroot};
use std::env;
use std::process::{Command, Stdio};

fn process(mut args: Vec<String>) -> Result<(), i32> {
    let mut prusti_driver_path = std::env::current_exe()
        .expect("current executable path invalid")
        .with_file_name("prusti-driver");
    if cfg!(windows) {
        prusti_driver_path.set_extension("exe");
    }

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
        add_to_loader_path(vec![rustlib_path, compiler_lib], &mut cmd);
    } else {
        add_to_loader_path(vec![compiler_lib], &mut cmd);
    }

    let has_no_color_arg = args
        .iter()
        .find(|&x| x == "--color" || x.starts_with("--color="))
        .is_none();
    if has_no_color_arg {
        cmd.args(&["--color", "always"]);
    }
    if !args.iter().any(|s| s == "--sysroot") {
        args.push("--sysroot".to_owned());
        args.push(
            prusti_sysroot
                .into_os_string()
                .into_string()
                .expect("sysroot is not a valid utf-8 string"),
        );
    };

    cmd.args(args);

    if env::var_os("PRUSTI_LOAD_ALL_PROC_MACRO_CRATES").is_some() {
        cmd.arg("-L");
        cmd.arg(format!(
            "dependency={}/deps",
            prusti_home
                .as_os_str()
                .to_str()
                .expect("the Prusti HOME path contains invalid UTF-8")
        ));
        cmd.arg("--extern");
        let prusti_contracts_path =
            get_latest_crate_artefact(&prusti_home, "prusti_contracts", "rlib");
        cmd.arg(format!("prusti_contracts={}", prusti_contracts_path));
        let dylib_extension = if cfg!(target_os = "macos") {
            "dylib"
        } else {
            "so"
        };
        let prusti_internal_path =
            get_latest_crate_artefact(&prusti_home, "prusti_contracts_internal", dylib_extension);
        cmd.arg("--extern");
        cmd.arg(format!(
            "prusti_contracts_internal={}",
            prusti_internal_path
        ));
    }
    // cmd.arg("-Zreport-delayed-bugs");
    // cmd.arg("-Ztreat-err-as-bug=1");

    let mut child = cmd
        .stdout(Stdio::inherit()) // do not filter stdout
        .stderr(Stdio::inherit()) // do not filter stderr
        .spawn()
        .expect("could not run prusti-driver");

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
