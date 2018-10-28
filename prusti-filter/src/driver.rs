#![feature(rustc_private)]
#![feature(box_syntax)]
#![feature(box_patterns)]

extern crate env_logger;
#[macro_use]
extern crate log;
extern crate rustc_driver;
extern crate rustc;
extern crate rustc_plugin;
extern crate syntax;

extern crate serde;
extern crate serde_json;
#[macro_use]
extern crate serde_derive;

extern crate prusti_interface;

mod crate_visitor;
mod validators;

use rustc_driver::driver::{CompileController, CompileState};
use rustc_driver::Compilation;
use std::env;
use std::fs;
use std::io::Write;
use std::process::Command;
use self::crate_visitor::{CrateVisitor, CrateStatus};
use validators::Validator;
use rustc::hir::intravisit::Visitor;


fn main() {
    env_logger::init();

    let exit_status = rustc_driver::run(move || {
        // Mostly copied from clippy

        let sys_root = option_env!("SYSROOT")
            .map(String::from)
            .or_else(|| std::env::var("SYSROOT").ok())
            .or_else(|| {
                let home = option_env!("RUSTUP_HOME").or(option_env!("MULTIRUST_HOME"));
                let toolchain = option_env!("RUSTUP_TOOLCHAIN").or(option_env!("MULTIRUST_TOOLCHAIN"));
                home.and_then(|home| toolchain.map(|toolchain| format!("{}/toolchains/{}", home, toolchain)))
            })
            .or_else(|| {
                Command::new("rustc")
                    .arg("--print")
                    .arg("sysroot")
                    .output()
                    .ok()
                    .and_then(|out| String::from_utf8(out.stdout).ok())
                    .map(|s| s.trim().to_owned())
            })
            .expect("need to specify SYSROOT env var during clippy compilation, or use rustup or multirust");

        // Setting RUSTC_WRAPPER causes Cargo to pass 'rustc' as the first argument.
        // We're invoking the compiler programmatically, so we ignore this/
        let mut orig_args: Vec<String> = env::args().collect();
        if orig_args.len() <= 1 {
            std::process::exit(1);
        }
        if orig_args[1] == "rustc" {
            // we still want to be able to invoke it normally though
            orig_args.remove(1);
        }

        // this conditional check for the --sysroot flag is there so users can call
        // `clippy_driver` directly
        // without having to pass --sysroot or anything
        let args: Vec<String> = if orig_args.iter().any(|s| s == "--sysroot") {
            orig_args.clone()
        } else {
            orig_args
                .clone()
                .into_iter()
                .chain(Some("--sysroot".to_owned()))
                .chain(Some(sys_root))
                .collect()
        };

        let mut controller = CompileController::basic();
        //controller.keep_ast = true;

        controller.after_analysis.callback = box |cs: &mut CompileState| {
            //let crate_name_env = env::var("CARGO_PKG_NAME").unwrap_or_default();
            //let crate_version_env = env::var("CARGO_PKG_VERSION").unwrap_or_default();
            let crate_name = cs.crate_name.unwrap();
            let tcx = cs.tcx.expect("no valid tcx");
            let mut cv = CrateVisitor {
                crate_name: crate_name,
                tcx,
                validator: Validator::new(tcx),
                crate_status: CrateStatus {
                    crate_name: String::from(crate_name),
                    functions: Vec::new(),
                },
            };

            // **Deep visit**: Want to scan for specific kinds of HIR nodes within
            // an item, but don't care about how item-like things are nested
            // within one another.
            tcx.hir.krate().visit_all_item_likes(&mut cv.as_deep_visitor());

            let data = serde_json::to_string_pretty(&cv.crate_status).unwrap();
            //let path = fs::canonicalize("../results.json").unwrap();

            // For rosetta without deleting root Cargo.toml:
            //let mut file = fs::OpenOptions::new()
                //.append(true)
                //.create(true)
                //.open("results.json")
                //.unwrap();
            //file.write_all(b"\n====================\n").unwrap();
            //file.write_all(&data.into_bytes()).unwrap();

            // For crates.io:
            fs::write("results.json", data).expect("Unable to write file");
        };

        // Stop compilation to save time. Do not produce binaries.
        controller.compilation_done.stop = Compilation::Stop;

        rustc_driver::run_compiler(&args, Box::new(controller), None, None)
    });
    std::process::exit(exit_status as i32);
}
