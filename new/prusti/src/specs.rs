use log::debug;
use proc_macro::bridge::client::ProcMacro;
use rustc_ast::ast;
use rustc_expand::proc_macro::AttrProcMacro;
use rustc_interface::interface::Compiler;
use rustc_metadata::creader::CStore;
use rustc_metadata::dynamic_lib::DynamicLibrary;
use rustc_middle::middle::cstore::CrateStore;
use rustc_resolve::Resolver;
use std::path::Path;

/// We report all errors via the compiler session, so no need to have a concrete
/// error type. We use `Err` only to signal that the error occurred and we
/// should terminate.
type SpecsResult<T = ()> = Result<T, ()>;

/// Rewrite the crate so that the compiler checks the specifications for us.
pub(crate) fn rewrite_crate(
    compiler: &Compiler,
    resolver: &mut Resolver,
    _krate: &mut ast::Crate,
    proc_macro_lib_path: &Path,
) -> SpecsResult {
    let _proc_macro = load_proc_macro(compiler, resolver.cstore(), proc_macro_lib_path)?;

    Ok(())
}

/// Load the procedural macro used for rewriting specifications.
///
/// The implementation is based on the
/// [dlsym_proc_macros](https://github.com/rust-lang/rust/blob/c1e05528696ca523055b0f7ce94b8033dcbaa39e/src/librustc_metadata/creader.rs#L599)
/// function implementation.
fn load_proc_macro(
    compiler: &Compiler,
    cstore: &CStore,
    proc_macro_lib_path: &Path,
) -> SpecsResult<Box<AttrProcMacro>> {
    let lib =
        DynamicLibrary::open(proc_macro_lib_path).expect("failed to load the contracts library");

    // Find the disambiguator of prusti_contracts_internal.
    let disambiguator = {
        let mut found = None;
        for crate_num in cstore.crates_untracked() {
            debug!(
                "Loaded crate: {}",
                cstore.crate_name_untracked(crate_num).as_str()
            );
            if cstore.crate_name_untracked(crate_num).as_str() == "prusti_contracts_internal" {
                assert!(
                    found.is_none(),
                    "found multiple versions of prusti_contracts"
                );
                found = Some(cstore.crate_disambiguator_untracked(crate_num));
            }
        }
        found.ok_or_else(|| {
            let mut warning = compiler
                .session()
                .struct_warn("`prusti_contracts_internal` crate not found");
            warning.note("Maybe `use prusti_contracts::*` is missing?");
            warning.emit();
        })?
    };

    // Compute the symbol of the proc macro declaration.
    let sym = compiler
        .session()
        .generate_proc_macro_decls_symbol(disambiguator);

    // Load the procedural macro symbol from the library.
    let decls = unsafe {
        let sym = lib
            .symbol(&sym)
            .expect("failed to construct proc macro decl symbol");
        *(sym as *const &[ProcMacro])
    };

    // Intentionally leak the dynamic library. We can't ever unload it
    // since the library can make things that will live arbitrarily long.
    std::mem::forget(lib);

    // We assume that the crate provides exactly one procedural macro.
    let proc_macro = if let proc_macro::bridge::client::ProcMacro::Attr { client, name } = decls[0]
    {
        assert_eq!(name, "expand_specs");
        Box::new(AttrProcMacro { client })
    } else {
        unreachable!();
    };

    Ok(proc_macro)
}
