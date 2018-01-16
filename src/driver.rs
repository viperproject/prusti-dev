#![feature(box_syntax)]
#![feature(rustc_private)]

extern crate env_logger;
extern crate getopts;
#[macro_use]
extern crate log;
extern crate prusti;
extern crate rustc;
extern crate rustc_driver;
extern crate rustc_errors;
extern crate syntax;

use rustc::session;
use rustc_driver::{driver, Compilation, CompilerCalls, RustcDefaultCalls};
use std::path::PathBuf;
use std::process::Command;
use syntax::ast;
use syntax::feature_gate::AttributeType;

struct PrustiCompilerCalls {
    default: RustcDefaultCalls,
}

impl PrustiCompilerCalls {
    fn new() -> Self {
        Self {
            default: RustcDefaultCalls,
        }
    }
}

impl<'a> CompilerCalls<'a> for PrustiCompilerCalls {
    fn early_callback(
        &mut self,
        matches: &getopts::Matches,
        sopts: &session::config::Options,
        cfg: &ast::CrateConfig,
        descriptions: &rustc_errors::registry::Registry,
        output: session::config::ErrorOutputType,
    ) -> Compilation {
        self.default
            .early_callback(matches, sopts, cfg, descriptions, output)
    }
    fn no_input(
        &mut self,
        matches: &getopts::Matches,
        sopts: &session::config::Options,
        cfg: &ast::CrateConfig,
        odir: &Option<PathBuf>,
        ofile: &Option<PathBuf>,
        descriptions: &rustc_errors::registry::Registry,
    ) -> Option<(session::config::Input, Option<PathBuf>)> {
        self.default
            .no_input(matches, sopts, cfg, odir, ofile, descriptions)
    }
    fn late_callback(
        &mut self,
        matches: &getopts::Matches,
        sess: &session::Session,
        crate_stores: &rustc::middle::cstore::CrateStore,
        input: &session::config::Input,
        odir: &Option<PathBuf>,
        ofile: &Option<PathBuf>,
    ) -> Compilation {
        self.default
            .late_callback(matches, sess, crate_stores, input, odir, ofile)
    }
    fn build_controller(&mut self, sess: &session::Session, matches: &getopts::Matches) -> driver::CompileController<'a> {
        let mut control = self.default.build_controller(sess, matches);
        //control.make_glob_map = ???
        //control.keep_ast = true;
        let old = std::mem::replace(&mut control.after_parse.callback, box |_| {});
        control.after_parse.callback = Box::new(move |state| {
            trace!("[after_parse.callback] enter");
            {
                let registry = state.registry.as_mut().unwrap();
                registry.register_attribute(
                    String::from("invariant"), AttributeType::Whitelisted);
                registry.register_attribute(
                    String::from("requires"), AttributeType::Whitelisted);
                registry.register_attribute(
                    String::from("ensures"), AttributeType::Whitelisted);
                registry.register_attribute(
                    String::from("__PRUSTI_SPEC"), AttributeType::Whitelisted);
                registry.register_attribute(
                    String::from("__PRUSTI_SPEC_PROC"), AttributeType::Whitelisted);
            }
            prusti::parser::rewrite_crate(state);
            trace!("[after_parse.callback] exit");
            old(state);
        });
        let old = std::mem::replace(&mut control.after_analysis.callback, box |_| {});
        control.after_analysis.callback = Box::new(move |state| {
            trace!("[after_analysis.callback] enter");
            trace!("[after_analysis.callback] exit");
            old(state);
        });
        control.after_analysis.stop = Compilation::Stop;
        control
    }
}

fn get_sysroot() -> String {
    Command::new("rustc")
                .arg("--print")
                .arg("sysroot")
                .output()
                .ok()
                .and_then(|out| String::from_utf8(out.stdout).ok())
                .map(|s| s.trim().to_owned())
                .expect("Failed to figure out SYSROOT.")
}

pub fn main() {
    env_logger::init().unwrap();
    trace!("[main] enter");
    let mut args: Vec<String> = std::env::args().collect();
    args.push("--sysroot".to_owned());
    args.push(get_sysroot());
    let mut prusti_compiler_calls = PrustiCompilerCalls::new();
    rustc_driver::in_rustc_thread(move || {
        let (result, _) = rustc_driver::run_compiler(
            &args, &mut prusti_compiler_calls, None, None);
        if let Err(session::CompileIncomplete::Errored(_)) = result {
            std::process::exit(1);
        }
    }).expect("rustc_thread failed");
    trace!("[main] exit");
}
