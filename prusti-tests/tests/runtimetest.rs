#![feature(custom_test_frameworks)]
#![test_runner(test_runner)]

use prusti_server::spawn_server_thread;
use std::{env, num::NonZeroUsize, path::PathBuf};
use ui_test::*;

// copied from compiletest. Maybe create a module with common utilities?
fn find_prusti_rustc_path() -> PathBuf {
    let target_directory = if cfg!(debug_assertions) {
        "debug"
    } else {
        "release"
    };
    let executable_name = if cfg!(windows) {
        "prusti-rustc.exe"
    } else {
        "prusti-rustc"
    };
    let local_prusti_rustc_path: PathBuf = ["target", target_directory, executable_name]
        .iter()
        .collect();
    if local_prusti_rustc_path.exists() {
        return local_prusti_rustc_path;
    }
    let workspace_prusti_rustc_path: PathBuf = ["..", "target", target_directory, executable_name]
        .iter()
        .collect();
    if workspace_prusti_rustc_path.exists() {
        return workspace_prusti_rustc_path;
    }
    panic!(
        "Could not find the {target_directory:?} prusti-rustc binary to be used in tests. \
        It might be that Prusti has not been compiled correctly."
    );
}

enum TestKind {
    RustcRuntimeChecks,
    RustcDeadCodeRemoval,
}

impl TestKind {
    fn build_config(&self, group_name: &str) -> Config {
        let path: PathBuf = ["tests", group_name].iter().collect();
        let prusti_path: PathBuf = find_prusti_rustc_path();
        let mut prusti_cmd = CommandBuilder {
            out_dir_flag: Some("--out-dir".into()),
            ..CommandBuilder::cmd(prusti_path)
        };

        match self {
            Self::RustcRuntimeChecks => {
                prusti_cmd
                    .envs
                    .push(("PRUSTI_FULL_COMPILATION".into(), Some("true".into())));
                prusti_cmd
                    .envs
                    .push(("PRUSTI_INSERT_RUNTIME_CHECKS".into(), Some("true".into())));
                prusti_cmd
                    .envs
                    .push(("PRUSTI_DEBUG_RUNTIME_CHECKS".into(), Some("true".into())));
            }
            Self::RustcDeadCodeRemoval => {
                prusti_cmd
                    .envs
                    .push(("PRUSTI_FULL_COMPILATION".into(), Some("true".into())));
                prusti_cmd
                    .envs
                    .push(("PRUSTI_REMOVE_DEAD_CODE".into(), Some("true".into())));
            }
        }

        let mut config = Config {
            program: prusti_cmd,
            edition: Some("2018".to_string()),
            ..Config::rustc(path)
        };
        // this filters out the uuid's for the printed messages that tell us
        // which tests are performed.
        config.stdout_filter(r"_([0-9, a-z]+) is performed", " is performed");
        if std::env::var_os("BLESS").is_some() {
            println!("It's a blessing :)");
            config.output_conflict_handling = OutputConflictHandling::Bless
        }
        config
    }
}

fn compile_and_run(group_name: &str, filter: &Option<String>, test_kind: TestKind) {
    let config = test_kind.build_config(group_name);

    // multiple threads lead to problems atm. If we want multiple threads, all
    // files need unique names.
    let mut args = Args::test().unwrap();
    args.threads = NonZeroUsize::new(1).unwrap();
    let _ = run_tests_generic(
        vec![config],
        args,
        move |path, args, config| {
            filter
                .as_ref()
                .map(|filter| path.display().to_string().contains(filter.as_str()))
                .unwrap_or(true)
                && default_file_filter(path, args, config)
        },
        default_per_file_config,
        status_emitter::Text::verbose(),
    );
}

fn test_runner(_tests: &[&()]) {
    let server_address = spawn_server_thread();
    env::set_var("PRUSTI_SERVER_ADDRESS", server_address.to_string());

    let filter = std::env::args().nth(1);
    println!("filter: {:?}", filter);
    // Cargo tests don't work at the moment
    // compile_and_run(
    //     &"runtime_checks_cargo",
    //     &filter,
    //     TestKind::CargoRuntimeChecks,
    // );
    compile_and_run(&"runtime_checks", &filter, TestKind::RustcRuntimeChecks);
    compile_and_run(
        &"mir_optimizations",
        &filter,
        TestKind::RustcDeadCodeRemoval,
    );
}
