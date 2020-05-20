#![feature(rustc_private)]

extern crate rustc_driver;
extern crate rustc_interface;
extern crate rustc_hir;
extern crate rustc_session;
extern crate rustc_ast;

use std::env;

use rustc_driver::Compilation;
use rustc_ast::mut_visit::MutVisitor;

struct PrustiCompilerCalls {

}

struct AstRewriter {}


use rustc_ast::ast::ItemKind;
impl rustc_ast::mut_visit::MutVisitor for AstRewriter {
    fn visit_item_kind(&mut self, item: &mut ItemKind) {
        // println!("Visit item: {:?}", item);
        match item {
            ItemKind::Fn(_, sig, _, body) => {
                // println!("Function: {:?}", sig);
                // *body = None;
            }
        _ => {
            rustc_ast::mut_visit::noop_visit_item_kind(item, self);
        },
        }
    }
}

impl rustc_driver::Callbacks for PrustiCompilerCalls {
    fn after_expansion<'tcx>(
        &mut self,
        compiler: &rustc_interface::interface::Compiler,
        queries: &'tcx rustc_interface::Queries<'tcx>,
    ) -> Compilation {
        compiler.session().abort_if_errors();
        // std::mem::drop(queries.expansion().unwrap().take());
        let (krate, _resolver, _lint_store) = &mut *queries.expansion().unwrap().peek_mut();

        let mut rewriter = AstRewriter {};
        rewriter.visit_crate(krate);
        rustc_driver::pretty::print_after_parsing(
            compiler.session(),
            compiler.input(),
            krate,
            rustc_session::config::PpMode::PpmSource(rustc_session::config::PpSourceMode::PpmNormal),
            None,
        );
        Compilation::Continue
    }

    fn after_analysis<'tcx>(
        &mut self,
        compiler: &rustc_interface::interface::Compiler,
        queries: &'tcx rustc_interface::Queries<'tcx>,
    ) -> Compilation {
        compiler.session().abort_if_errors();

        queries.global_ctxt().unwrap().peek_mut().enter(|_tcx| {
            println!("After analysis!");
            // let (entry_def_id, _) = tcx.entry_fn(LOCAL_CRATE).expect("no main function found!");
            // let mut config = self.miri_config.clone();

            // Add filename to `miri` arguments.
            // config.args.insert(0, compiler.input().filestem().to_string());

            // if let Some(return_code) = miri::eval_main(tcx, entry_def_id.to_def_id(), config) {
            //     std::process::exit(
            //         // i32::try_from(return_code).expect("Return value was too large!"),

            //     );
            // }
            // std::process::exit(0);
        });

        compiler.session().abort_if_errors();

        Compilation::Stop
    }
}

fn init_early_loggers() {
    // Note that our `extern crate log` is *not* the same as rustc's; as a result, we have to
    // initialize them both, and we always initialize `miri`'s first.
    let env = env_logger::Env::new().filter("MIRI_LOG").write_style("MIRI_LOG_STYLE");
    env_logger::init_from_env(env);
    // We only initialize `rustc` if the env var is set (so the user asked for it).
    // If it is not set, we avoid initializing now so that we can initialize
    // later with our custom settings, and *not* log anything for what happens before
    // `miri` gets started.
    if env::var_os("RUSTC_LOG").is_some() {
        rustc_driver::init_rustc_env_logger();
    }
}

/// Returns the "default sysroot" that Miri will use if no `--sysroot` flag is set.
/// Should be a compile-time constant.
fn compile_time_sysroot() -> Option<String> {
    if option_env!("RUSTC_STAGE").is_some() {
        // This is being built as part of rustc, and gets shipped with rustup.
        // We can rely on the sysroot computation in librustc_session.
        return None;
    }
    // For builds outside rustc, we need to ensure that we got a sysroot
    // that gets used as a default.  The sysroot computation in librustc_session would
    // end up somewhere in the build dir (see `get_or_default_sysroot`).
    // Taken from PR <https://github.com/Manishearth/rust-clippy/pull/911>.
    let home = option_env!("RUSTUP_HOME").or(option_env!("MULTIRUST_HOME"));
    let toolchain = option_env!("RUSTUP_TOOLCHAIN").or(option_env!("MULTIRUST_TOOLCHAIN"));
    Some(match (home, toolchain) {
        (Some(home), Some(toolchain)) => format!("{}/toolchains/{}", home, toolchain),
        _ => option_env!("RUST_SYSROOT")
            .expect("To build Miri without rustup, set the `RUST_SYSROOT` env var at build time")
            .to_owned(),
    })
}

/// Execute a compiler with the given CLI arguments and callbacks.
fn run_compiler(mut args: Vec<String>, callbacks: &mut (dyn rustc_driver::Callbacks + Send)) -> ! {
    // Make sure we use the right default sysroot. The default sysroot is wrong,
    // because `get_or_default_sysroot` in `librustc_session` bases that on `current_exe`.
    //
    // Make sure we always call `compile_time_sysroot` as that also does some sanity-checks
    // of the environment we were built in.
    // FIXME: Ideally we'd turn a bad build env into a compile-time error via CTFE or so.
    if let Some(sysroot) = compile_time_sysroot() {
        let sysroot_flag = "--sysroot";
        if !args.iter().any(|e| e == sysroot_flag) {
            // We need to overwrite the default that librustc_session would compute.
            args.push(sysroot_flag.to_owned());
            args.push(sysroot);
        }
    }

    // Some options have different defaults in Miri than in plain rustc; apply those by making
    // them the first arguments after the binary name (but later arguments can overwrite them).
    // args.splice(1..1, miri::miri_default_args().iter().map(ToString::to_string));

    // Invoke compiler, and handle return code.
    let exit_code = rustc_driver::catch_with_exit_code(move || {
        rustc_driver::run_compiler(&args, callbacks, None, None)
    });
    std::process::exit(exit_code)
}

fn main() {
    rustc_driver::install_ice_hook();

    // If the environment asks us to actually be rustc, then do that.
    if env::var_os("MIRI_BE_RUSTC").is_some() {
        rustc_driver::init_rustc_env_logger();
        // We cannot use `rustc_driver::main` as we need to adjust the CLI arguments.
        let mut callbacks = rustc_driver::TimePassesCallbacks::default();
        run_compiler(env::args().collect(), &mut callbacks)
    }

    // Init loggers the Miri way.
    init_early_loggers();

    let rustc_args = env::args().collect();
    run_compiler(rustc_args, &mut PrustiCompilerCalls { })
}