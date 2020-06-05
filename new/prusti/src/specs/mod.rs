mod node_id_rewriter;

use crate::specs::node_id_rewriter::MutVisitor;
use log::debug;
use proc_macro::bridge::client::ProcMacro;
use rustc_ast::ast;
use rustc_ast::token;
use rustc_ast::tokenstream::{self, TokenStreamBuilder};
use rustc_expand::base::AttrProcMacro as AttrProcMacroTrait;
use rustc_expand::proc_macro::AttrProcMacro;
use rustc_interface::interface::Compiler;
use rustc_metadata::creader::CStore;
use rustc_metadata::dynamic_lib::DynamicLibrary;
use rustc_middle::middle::cstore::CrateStore;
use rustc_resolve::Resolver;
use rustc_span::{MultiSpan, DUMMY_SP};
use std::path::Path;

/// We report all errors via the compiler session, so no need to have a concrete
/// error type. We use `Err` only to signal that the error occurred and we
/// should terminate.
type SpecsResult<T = ()> = Result<T, ()>;

/// Rewrite the crate so that the compiler checks the specifications for us.
pub(crate) fn rewrite_crate(
    compiler: &Compiler,
    resolver: &mut Resolver,
    crate_name: String,
    krate: &mut ast::Crate,
    proc_macro_lib_path: &Path,
    print_desugared_specs: bool,
) -> SpecsResult {
    let proc_macro = load_proc_macro(compiler, resolver.cstore(), proc_macro_lib_path)?;

    let mut visitor = node_id_rewriter::NodeIdRewriter::new();

    // Collect ids of the existing items so that we can restore them later.
    visitor.visit_crate(krate);

    run_proc_macro(compiler, krate, crate_name, resolver, proc_macro)?;

    if print_desugared_specs {
        rustc_driver::pretty::print_after_parsing(
            compiler.session(),
            compiler.input(),
            krate,
            rustc_session::config::PpMode::PpmSource(
                rustc_session::config::PpSourceMode::PpmNormal,
            ),
            None,
        );
    }

    visitor.set_phase_generate_fresh_ids(resolver);
    visitor.visit_crate(krate);
    let compiler_errors = visitor.get_compiler_errors();
    if !compiler_errors.is_empty() {
        let session = compiler.session();
        for (msg, span) in compiler_errors {
            let mut error = session.struct_span_err(MultiSpan::from_span(*span), msg);
            error.emit();
        }
        return Err(());
    }

    visitor.set_phase_register_fresh_ids();
    visitor.visit_crate(krate);

    Ok(())
}

/// Rewrite the crate by running the procedural macro on it.
fn run_proc_macro(
    compiler: &Compiler,
    krate: &mut ast::Crate,
    crate_name: String,
    resolver: &mut Resolver,
    proc_macro: Box<AttrProcMacro>,
) -> SpecsResult<()> {
    // Get the crate tokens. The code is based on
    // https://github.com/rust-lang/rust/blob/5943351d0eb878c1cb5af42b9e85e101d8c58ed7/src/librustc_expand/expand.rs#L703-L718.
    let parse_sess = &compiler.session().parse_sess;
    let mut tokens = TokenStreamBuilder::new();
    let old_items = std::mem::replace(&mut krate.module.items, Vec::new());
    for mut item in old_items {
        let span = item.span;
        let attrs = std::mem::replace(&mut item.attrs, Vec::new());
        for attr in attrs {
            attr.to_tokens(&mut tokens);
        }
        let item_tokens = rustc_parse::nt_to_tokenstream(&token::NtItem(item), parse_sess, span);
        tokens.push(item_tokens);
    }

    let mut cx = rustc_expand::base::ExtCtxt::new(
        parse_sess,
        rustc_expand::expand::ExpansionConfig::default(crate_name),
        resolver,
        None,
    );
    let expn_id = cx.resolver.expansion_for_ast_pass(
        DUMMY_SP,
        rustc_span::hygiene::AstPass::ProcMacroHarness,
        &[],
        None,
    );
    cx.current_expansion.id = expn_id;

    let inner_tokens = rustc_ast::tokenstream::TokenStream::new(vec![]);
    let tok_result = match proc_macro.expand(&mut cx, DUMMY_SP, inner_tokens, tokens.build()) {
        Err(_err) => {
            return Err(());
        }
        Ok(ts) => ts,
    };
    let mut parser = cx.new_parser_from_tts(tok_result);
    let fragment = rustc_expand::expand::parse_ast_fragment(
        &mut parser,
        rustc_expand::expand::AstFragmentKind::Items,
    )
    .expect("TODO");

    krate.module.items = fragment.make_items().to_vec();

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
        found
    };

    // Compute the symbol of the proc macro declaration.
    let sym = if let Some(disambiguator) = disambiguator {
        compiler
            .session()
            .generate_proc_macro_decls_symbol(disambiguator)
    } else {
        if let Some(symbol) = std::env::var("PRUSTI_CONTRACTS_MACRO_SYMBOL").ok() {
            symbol
        } else {
            let mut err = compiler
                .session()
                .struct_err("could not find the rewriting procedural macro");
            err.help(
                "either add `extern crate prusti_contracts` or set `PRUSTI_CONTRACTS_MACRO_SYMBOL`",
            );
            err.emit();
            return Err(());
        }
    };

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

trait ToTokens {
    fn to_tokens(&self, tokens: &mut TokenStreamBuilder);
}

impl ToTokens for ast::Attribute {
    fn to_tokens(&self, tokens: &mut TokenStreamBuilder) {
        match self.style {
            ast::AttrStyle::Outer => {
                tokens.push(tokenstream::TokenTree::token(token::Pound, self.span));
            }
            ast::AttrStyle::Inner => {
                unimplemented!();
            }
        }
        let mut brackets = tokenstream::TokenStreamBuilder::new();
        self.kind.to_tokens(&mut brackets);
        let delim_span = tokenstream::DelimSpan::from_single(self.span);
        tokens.push(tokenstream::TokenTree::Delimited(
            delim_span,
            token::DelimToken::Bracket,
            brackets.build(),
        ));
    }
}

impl ToTokens for ast::AttrKind {
    fn to_tokens(&self, tokens: &mut TokenStreamBuilder) {
        match self {
            ast::AttrKind::Normal(item) => {
                item.to_tokens(tokens);
            }
            ast::AttrKind::DocComment(_symbol) => {
                unimplemented!();
            }
        }
    }
}

impl ToTokens for ast::AttrItem {
    fn to_tokens(&self, tokens: &mut TokenStreamBuilder) {
        self.path.to_tokens(tokens);
        self.args.to_tokens(tokens)
    }
}

impl ToTokens for ast::Path {
    fn to_tokens(&self, tokens: &mut TokenStreamBuilder) {
        let mut trees = Vec::new();
        for segment in &self.segments {
            if segment.args.is_some() {
                unimplemented!();
            }
            let ident = segment.ident;
            let token = token::Ident(ident.name, ident.as_str().starts_with("r#"));
            trees.push(tokenstream::TokenTree::token(token, ident.span));
            trees.push(tokenstream::TokenTree::token(token::ModSep, self.span));
        }
        // Remove the last `::`
        trees.pop();
        for tree in trees {
            tokens.push(tree);
        }
    }
}

impl ToTokens for ast::MacArgs {
    fn to_tokens(&self, tokens: &mut TokenStreamBuilder) {
        tokens.push(self.outer_tokens());
    }
}
