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

use rustc_driver::RustcDefaultCalls;
use rustc_driver::driver::{CompileController, CompileState};
use rustc_driver::Compilation;
use std::env;
use std::fs;
use self::crate_visitor::{CrateVisitor, CrateStatus};
use validators::Validator;
use rustc::hir::intravisit::Visitor;
use prusti_interface::constants::PRUSTI_SPEC_ATTR;
use prusti_interface::sysroot::current_sysroot;


fn main() {
    env_logger::init();

    let exit_status = rustc_driver::run(move || {
        let mut args: Vec<String> = env::args().collect();

        let prusti_disabled = (!args.is_empty() && args[1] == "rustc")
            && !args.iter().any(|s| s == "--emit=dep-info,metadata");

        // Setting RUSTC_WRAPPER causes Cargo to pass 'rustc' as the first argument.
        // We're invoking the compiler programmatically, so we ignore this
        if !args.is_empty() && args[1] == "rustc" {
            args.remove(1);
        }

        // Early exit
        if prusti_disabled {
            let default_compiler_calls = Box::new(RustcDefaultCalls);
            return rustc_driver::run_compiler(&args, default_compiler_calls, None, None);
        }

        // this conditional check for the --sysroot flag is there so users can call
        // `prusti-filter` directly without having to pass --sysroot or anything
        if !args.iter().any(|s| s == "--sysroot") {
            let sys_root = current_sysroot()
                .expect("need to specify SYSROOT env var during prusti-driver compilation, or use rustup or multirust");
            debug!("Using sys_root='{}'", sys_root);
            args.push("--sysroot".to_owned());
            args.push(sys_root);
        };

        // Arguments required by Prusti (Rustc may produce different MIR)
        args.push("-Zborrowck=mir".to_owned());
        args.push("-Zpolonius".to_owned());

        let mut controller = CompileController::basic();
        //controller.keep_ast = true;

        let old = std::mem::replace(&mut controller.after_parse.callback, box |_| {});
        controller.after_parse.callback = box move |state| {
            prusti_interface::parser::register_attributes(state);
            let _ = prusti_interface::parser::rewrite_crate(state);
            info!("Parsing of annotations successful");
            old(state);
        };

        let old = std::mem::replace(&mut controller.after_analysis.callback, box |_| {});
        controller.after_analysis.callback = box move |state: &mut CompileState| {
            //let crate_name_env = env::var("CARGO_PKG_NAME").unwrap_or_default();
            //let crate_version_env = env::var("CARGO_PKG_VERSION").unwrap_or_default();
            let crate_name = state.crate_name.unwrap();
            let tcx = state.tcx.expect("no valid tcx");
            let mut crate_visitor = CrateVisitor {
                crate_name: crate_name,
                tcx,
                validator: Validator::new(tcx),
                crate_status: CrateStatus {
                    crate_name: String::from(crate_name),
                    functions: Vec::new(),
                },
                source_map: state.session.parse_sess.codemap()
            };

            // **Deep visit**: Want to scan for specific kinds of HIR nodes within
            // an item, but don't care about how item-like things are nested
            // within one another.
            tcx.hir.krate().visit_all_item_likes(&mut crate_visitor.as_deep_visitor());

            let data = serde_json::to_string_pretty(&crate_visitor.crate_status).unwrap();
            //let path = fs::canonicalize("../prusti-filter-results.json").unwrap();

            // For rosetta without deleting root Cargo.toml:
            //let mut file = fs::OpenOptions::new()
                //.append(true)
                //.create(true)
                //.open("prusti-filter-results.json")
                //.unwrap();
            //file.write_all(b"\n====================\n").unwrap();
            //file.write_all(&data.into_bytes()).unwrap();

            // Write result
            let result_path = "prusti-filter-results.json";
            fs::write(result_path, data).expect("Unable to write file");

            info!(
                "Filtering successful. The result of the filtering has been stored to '{}'.",
                result_path
            );
            old(state);
        };

        controller.after_analysis.stop = Compilation::Stop;

        rustc_driver::run_compiler(&args, Box::new(controller), None, None)
    });
    std::process::exit(exit_status as i32);
}
