use std::process::Command;

fn main(){
    if let Err(code) = process(std::env::args().skip(1)) {
        std::process::exit(code);
    }
}

fn process<I>(args: I) -> Result<(), i32>
where
    I: Iterator<Item = String>,
{
    let mut prusti_filter_path = std::env::current_exe()
        .expect("current executable path invalid")
        .with_file_name("prusti-filter");
    if cfg!(windows) {
        prusti_filter_path.set_extension("exe");
    }

    let exit_status = Command::new("cargo".to_string())
        .arg("check")
        .args(args)
        .env("RUSTC_WRAPPER", prusti_filter_path)
        .status()
        .expect("could not run cargo");

    if exit_status.success() {
        Ok(())
    } else {
        Err(exit_status.code().unwrap_or(-1))
    }
}
