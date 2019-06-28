use std::path::{PathBuf, Path};
use std::env;

pub fn cargo_home() -> Option<PathBuf> {
    env::var("CARGO_HOME").ok()
        .map(|x| PathBuf::from(x))
        .or(
            env::home_dir().map(|x| x.join(".cargo"))
        )
}

/// Is it likely that cargo calling Prusti on a dependency crate?
/// * `args`: the arguments of the compiler call
pub fn is_rustc_compiling_a_dependency_crate(args: &Vec<String>) -> bool {
    if let Some(cargo_home) = cargo_home() {
        args.iter().any(|arg| {
            Path::new(arg).starts_with(&cargo_home)
        })
    } else {
        false
    }
}
