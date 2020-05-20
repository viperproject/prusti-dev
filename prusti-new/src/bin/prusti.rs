#![feature(rustc_private)]
#![feature(proc_macro_internals)]

extern crate rustc_driver;
extern crate rustc_interface;
extern crate rustc_hir;
extern crate rustc_session;
extern crate rustc_ast;
extern crate rustc_metadata;
extern crate rustc_data_structures;
extern crate proc_macro;
extern crate rustc_middle;
extern crate rustc_expand;
extern crate rustc_ast_pretty;

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
                //
                // Can I get expander?
                // https://doc.rust-lang.org/nightly/nightly-rustc/src/rustc_expand/expand.rs.html#703-718
                //
                // Yes:
                // https://doc.rust-lang.org/nightly/nightly-rustc/rustc_metadata/creader/struct.CrateLoader.html#method.load_proc_macro
                //
                // Can I get CrateLocator?
                //
                // Can I get CrateLoader?
                // https://doc.rust-lang.org/nightly/nightly-rustc/rustc_interface/interface/struct.BoxedResolver.html#method.access
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
        let (krate, resolver, _lint_store) = &mut *queries.expansion().unwrap().peek_mut();


        for item in &mut krate.module.items {
            match &item.kind {
                ItemKind::ExternCrate(..) |
                ItemKind::Use(..) => {
                    continue;
                }
                _ => {
                }
            }
            let tokens = item.tokens.as_ref().unwrap_or_else(|| {
                unimplemented!("unsupported kind: {:?}", item.kind);
            });
            println!("tokens: {}", rustc_ast_pretty::pprust::tts_to_string(tokens.clone()));
            for attr in &item.attrs {
                // TODO: Convert the attribute to the token stream and glue with the item's token stream.
                // https://doc.rust-lang.org/nightly/nightly-rustc/rustc_ast/ast/struct.AttrItem.html
                println!("attr: {:?}", attr.get_normal_item());
            }
        }

        let output_dir = env!("OUT_DIR");
        println!("output dir: {}", output_dir);
        let mut deps_dir_path = std::path::PathBuf::from(output_dir);
        deps_dir_path.push("../../../deps");

        println!("depds dir: {:?}", deps_dir_path);

        let path = std::fs::read_dir(deps_dir_path).unwrap().map(|result| result.unwrap())
        .filter(|entry| {
            let file_name = entry.file_name();
            let file_name = file_name.to_string_lossy();
            file_name.starts_with("libprusti_contracts_internal-")
        && file_name.ends_with(".so")
    })
        .max_by_key(|entry| entry.metadata().unwrap().modified().unwrap())
        .map(|entry| entry.path())
        .expect("could not locate prusti-contracts-internal");



        use rustc_metadata::dynamic_lib::DynamicLibrary;
        // let path = env::current_dir().unwrap().join("TODO");
        let lib = DynamicLibrary::open(&path).expect("failed to load the contracts library");
        // let fingerprint: rustc_data_structures::fingerprint::Fingerprint = unsafe { std::mem::transmute((1u64, 2u64))};
        // let disambiguator: rustc_session::CrateDisambiguator = fingerprint.into();


        // TODO: Use cargo_metadata to locate procedural macros with build.rs
        // and create a constant with information for each of them (global path,
        // symbol name, etc.)
        // Symbol name: https://doc.rust-lang.org/nightly/nightly-rustc/src/rustc_session/session.rs.html#690-692
        let disambiguator = (*resolver.borrow().borrow_mut()).access(|resolver| {
            use rustc_middle::middle::cstore::CrateStore;
            let cstore = resolver.cstore();
            let mut found = None;
            for crate_num in cstore.crates_untracked() {
                if cstore.crate_name_untracked(crate_num).as_str() == "prusti_contracts_internal" {
                    assert!(found.is_none(), "found multiple versions of prusti_contracts");
                    found = Some(cstore.crate_disambiguator_untracked(crate_num));
                }
            }
            found.expect("prusti_contracts_internal crate not found")
        });

        // https://github.com/rust-lang/rust/blob/c1e05528696ca523055b0f7ce94b8033dcbaa39e/src/librustc_metadata/creader.rs#L599
        let sym = compiler.session().generate_proc_macro_decls_symbol(disambiguator);
        let decls = unsafe {
            let sym = lib.symbol(&sym).expect("failed to construct proc macro decl symbol");
            *(sym as *const &[proc_macro::bridge::client::ProcMacro])
        };
        // Intentionally leak the dynamic library. We can't ever unload it
        // since the library can make things that will live arbitrarily long.
        std::mem::forget(lib);

        // TODO: https://github.com/rust-lang/rust/blob/bad3bf622bded50a97c0a54e29350eada2a3a169/src/librustc_metadata/rmeta/decoder.rs#L704-L706
        // We assume that the crate provides exactly one procedural macro.
        let expander = if let proc_macro::bridge::client::ProcMacro::Attr { client, .. } = decls[0] {
            // assert_eq!(name, "expected name");
            Box::new(rustc_expand::proc_macro::AttrProcMacro { client })
        } else {
            unreachable!();
        };

        (*resolver.borrow().borrow_mut()).access(|resolver| {
        // cx: &'a mut ExtCtxt<'b>,
        let parse_sess = &compiler.session().parse_sess;
        let mut cx =rustc_expand::base::ExtCtxt::new(
            parse_sess,
            rustc_expand::expand::ExpansionConfig::default(queries.crate_name().unwrap().peek().clone()),
            resolver,
            None,
        );

        // TODO: https://github.com/rust-lang/rust/blob/5943351d0eb878c1cb5af42b9e85e101d8c58ed7/src/librustc_expand/expand.rs#L703-L718
        let mut new_items = Vec::new();
        for item in &mut krate.module.items {
            use crate::rustc_expand::base::AttrProcMacro;
            let tokens = item.tokens.as_mut().unwrap().clone();
            let inner_tokens = rustc_ast::tokenstream::TokenStream::new(vec![]);
            let tok_result = match expander.expand(&mut cx, item.span, inner_tokens, tokens) {
                Err(_) => unimplemented!(),
                //return ExpandResult::Ready(fragment_kind.dummy(span)),
                Ok(ts) => ts,
            };
            let mut parser = cx.new_parser_from_tts(tok_result);
            let fragment = rustc_expand::expand::parse_ast_fragment(&mut parser, rustc_expand::expand::AstFragmentKind::Items).expect("TODO");
            match fragment {
                rustc_expand::expand::AstFragment::Items(items) => {
                    new_items.extend(items);
                }
                _ => {}
            }
        }
        std::mem::swap(&mut new_items, &mut krate.module.items);
    });


        // let mut rewriter = AstRewriter {};
        // rewriter.visit_crate(krate);
        // rustc_driver::pretty::print_after_parsing(
        //     compiler.session(),
        //     compiler.input(),
        //     krate,
        //     rustc_session::config::PpMode::PpmSource(rustc_session::config::PpSourceMode::PpmNormal),
        //     None,
        // );
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