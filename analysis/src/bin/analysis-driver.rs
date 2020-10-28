#![feature(rustc_private)]

/// Source: https://github.com/rust-lang/miri/blob/master/benches/helpers/miri_helper.rs

extern crate rustc_driver;
extern crate rustc_hir;
extern crate rustc_interface;
extern crate rustc_middle;

use rustc_middle::ty;
use rustc_hir::def_id::LOCAL_CRATE;
use rustc_driver::Compilation;
use rustc_interface::{interface, Queries};
use analysis::Analyzer;
use analysis::abstract_domains::ReachingDefsState;
use std::path::PathBuf;

struct OurCompilerCalls;

impl rustc_driver::Callbacks for OurCompilerCalls {
    fn after_analysis<'tcx>(
        &mut self,
        compiler: &interface::Compiler,
        queries: &'tcx Queries<'tcx>,
    ) -> Compilation {
        compiler.session().abort_if_errors();

        queries.global_ctxt().unwrap().peek_mut().enter(|tcx| {
            let (main_def_id, _) = tcx.entry_fn(LOCAL_CRATE)
                .expect("no main or start function found");
            let analyzer = Analyzer::new(tcx);
            let main_body = tcx.mir_promoted(
                ty::WithOptConstParam::unknown(main_def_id)
            ).0.borrow();
            // TODO: switch analysis based on some flag or envirnoment variable
            let result = analyzer.run_fwd_analysis::<ReachingDefsState>(&main_body);
            // TODO: dump the result to stdout (e.g. using the serde library)
        });

        compiler.session().abort_if_errors();

        Compilation::Stop
    }
}

fn find_sysroot() -> String {
    // Taken from https://github.com/Manishearth/rust-clippy/pull/911.
    let home = option_env!("RUSTUP_HOME").or(option_env!("MULTIRUST_HOME"));
    let toolchain = option_env!("RUSTUP_TOOLCHAIN").or(option_env!("MULTIRUST_TOOLCHAIN"));
    match (home, toolchain) {
        (Some(home), Some(toolchain)) => format!("{}/toolchains/{}", home, toolchain),
        _ => option_env!("RUST_SYSROOT")
            .expect("need to specify RUST_SYSROOT env var or use rustup or multirust")
            .to_owned(),
    }
}

fn main() {
    let args: Vec<_> = std::env::args().collect();
    let mut callbacks = OurCompilerCalls;
    // Invoke compiler, and handle return code.
    let exit_code = rustc_driver::catch_with_exit_code(move || {
        rustc_driver::run_compiler(&args, &mut callbacks, None, None, None)
    });
    std::process::exit(exit_code)
}
