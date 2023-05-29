#![cfg_attr(not(feature = "prusti"), no_std)]
use proc_macro::TokenStream;

// -----------------------
// --- PRUSTI DISABLED ---

#[cfg(not(feature = "prusti"))]
#[proc_macro_attribute]
pub fn requires(_attr: TokenStream, tokens: TokenStream) -> TokenStream {
    tokens
}

/// FIXME: Remove
#[cfg(not(feature = "prusti"))]
#[proc_macro_attribute]
pub fn not_require(_attr: TokenStream, tokens: TokenStream) -> TokenStream {
    tokens
}

#[cfg(not(feature = "prusti"))]
#[proc_macro_attribute]
pub fn invariant(_attr: TokenStream, tokens: TokenStream) -> TokenStream {
    tokens
}

#[cfg(not(feature = "prusti"))]
#[proc_macro_attribute]
pub fn structural_invariant(_attr: TokenStream, tokens: TokenStream) -> TokenStream {
    tokens
}

#[cfg(not(feature = "prusti"))]
#[proc_macro_attribute]
pub fn broken_invariant(_attr: TokenStream, tokens: TokenStream) -> TokenStream {
    tokens
}

#[cfg(not(feature = "prusti"))]
#[proc_macro_attribute]
pub fn ensures(_attr: TokenStream, tokens: TokenStream) -> TokenStream {
    tokens
}

/// FIXME: Remove
#[cfg(not(feature = "prusti"))]
#[proc_macro_attribute]
pub fn not_ensure(_attr: TokenStream, tokens: TokenStream) -> TokenStream {
    tokens
}

#[cfg(not(feature = "prusti"))]
#[proc_macro_attribute]
pub fn after_expiry(_attr: TokenStream, tokens: TokenStream) -> TokenStream {
    tokens
}

#[cfg(not(feature = "prusti"))]
#[proc_macro_attribute]
pub fn assert_on_expiry(_attr: TokenStream, tokens: TokenStream) -> TokenStream {
    tokens
}

#[cfg(not(feature = "prusti"))]
#[proc_macro_attribute]
pub fn pure(_attr: TokenStream, tokens: TokenStream) -> TokenStream {
    tokens
}

#[cfg(not(feature = "prusti"))]
#[proc_macro_attribute]
pub fn trusted(_attr: TokenStream, tokens: TokenStream) -> TokenStream {
    tokens
}

#[cfg(not(feature = "prusti"))]
#[proc_macro_attribute]
pub fn verified(_attr: TokenStream, tokens: TokenStream) -> TokenStream {
    tokens
}

#[cfg(not(feature = "prusti"))]
#[proc_macro_attribute]
pub fn no_panic(_attr: TokenStream, tokens: TokenStream) -> TokenStream {
    tokens
}

#[cfg(not(feature = "prusti"))]
#[proc_macro_attribute]
pub fn no_panic_ensures_postcondition(_attr: TokenStream, tokens: TokenStream) -> TokenStream {
    tokens
}

#[cfg(not(feature = "prusti"))]
#[proc_macro]
pub fn body_invariant(_tokens: TokenStream) -> TokenStream {
    TokenStream::new()
}

#[cfg(not(feature = "prusti"))]
#[proc_macro]
pub fn prusti_assert(_tokens: TokenStream) -> TokenStream {
    TokenStream::new()
}

#[cfg(not(feature = "prusti"))]
#[proc_macro]
pub fn prusti_structural_assert(_tokens: TokenStream) -> TokenStream {
    TokenStream::new()
}

#[cfg(not(feature = "prusti"))]
#[proc_macro]
pub fn prusti_assume(_tokens: TokenStream) -> TokenStream {
    TokenStream::new()
}

#[cfg(not(feature = "prusti"))]
#[proc_macro]
pub fn prusti_refute(_tokens: TokenStream) -> TokenStream {
    TokenStream::new()
}

#[cfg(not(feature = "prusti"))]
#[proc_macro]
pub fn prusti_structural_assume(_tokens: TokenStream) -> TokenStream {
    TokenStream::new()
}

#[cfg(not(feature = "prusti"))]
#[proc_macro]
pub fn materialize_predicate(_tokens: TokenStream) -> TokenStream {
    TokenStream::new()
}

#[cfg(not(feature = "prusti"))]
#[proc_macro]
pub fn quantified_predicate(_tokens: TokenStream) -> TokenStream {
    TokenStream::new()
}

#[cfg(not(feature = "prusti"))]
#[proc_macro_attribute]
pub fn refine_trait_spec(_attr: TokenStream, tokens: TokenStream) -> TokenStream {
    tokens
}

#[cfg(not(feature = "prusti"))]
#[proc_macro_attribute]
pub fn extern_spec(_attr: TokenStream, _tokens: TokenStream) -> TokenStream {
    TokenStream::new()
}

#[cfg(not(feature = "prusti"))]
#[proc_macro]
pub fn predicate(_tokens: TokenStream) -> TokenStream {
    TokenStream::new()
}

#[cfg(not(feature = "prusti"))]
#[proc_macro_attribute]
pub fn model(_attr: TokenStream, _tokens: TokenStream) -> TokenStream {
    TokenStream::new()
}

#[cfg(not(feature = "prusti"))]
#[proc_macro_attribute]
pub fn refine_spec(_attr: TokenStream, tokens: TokenStream) -> TokenStream {
    tokens
}

#[cfg(not(feature = "prusti"))]
#[proc_macro]
pub fn ghost(_tokens: TokenStream) -> TokenStream {
    TokenStream::new()
}

#[cfg(not(feature = "prusti"))]
#[proc_macro]
pub fn on_drop_unwind(_tokens: TokenStream) -> TokenStream {
    TokenStream::new()
}

#[cfg(not(feature = "prusti"))]
#[proc_macro]
pub fn with_finally(_tokens: TokenStream) -> TokenStream {
    TokenStream::new()
}

#[cfg(not(feature = "prusti"))]
#[proc_macro]
pub fn checked(_tokens: TokenStream) -> TokenStream {
    TokenStream::new()
}

#[cfg(not(feature = "prusti"))]
#[proc_macro]
pub fn checked(_tokens: TokenStream) -> TokenStream {
    TokenStream::new()
}

#[cfg(not(feature = "prusti"))]
#[proc_macro_attribute]
pub fn print_counterexample(_attr: TokenStream, tokens: TokenStream) -> TokenStream {
    tokens
}

#[cfg(not(feature = "prusti"))]
#[proc_macro_attribute]
pub fn terminates(_attr: TokenStream, _tokens: TokenStream) -> TokenStream {
    TokenStream::new()
}

#[cfg(not(feature = "prusti"))]
#[proc_macro]
pub fn body_variant(_tokens: TokenStream) -> TokenStream {
    TokenStream::new()
}

#[cfg(not(feature = "prusti"))]
#[proc_macro]
pub fn manually_manage(_tokens: TokenStream) -> TokenStream {
    TokenStream::new()
}

#[cfg(not(feature = "prusti"))]
#[proc_macro]
pub fn pack(_tokens: TokenStream) -> TokenStream {
    TokenStream::new()
}

#[cfg(not(feature = "prusti"))]
#[proc_macro]
pub fn unpack(_tokens: TokenStream) -> TokenStream {
    TokenStream::new()
}

#[cfg(not(feature = "prusti"))]
#[proc_macro]
pub fn obtain(_tokens: TokenStream) -> TokenStream {
    TokenStream::new()
}

#[cfg(not(feature = "prusti"))]
#[proc_macro]
pub fn pack_ref(_tokens: TokenStream) -> TokenStream {
    TokenStream::new()
}

#[cfg(not(feature = "prusti"))]
#[proc_macro]
pub fn unpack_ref(_tokens: TokenStream) -> TokenStream {
    TokenStream::new()
}

#[cfg(not(feature = "prusti"))]
#[proc_macro]
pub fn pack_mut_ref(_tokens: TokenStream) -> TokenStream {
    TokenStream::new()
}

#[cfg(not(feature = "prusti"))]
#[proc_macro]
pub fn unpack_mut_ref(_tokens: TokenStream) -> TokenStream {
    TokenStream::new()
}

#[cfg(not(feature = "prusti"))]
#[proc_macro]
pub fn take_lifetime(_tokens: TokenStream) -> TokenStream {
    TokenStream::new()
}

#[cfg(not(feature = "prusti"))]
#[proc_macro]
pub fn set_lifetime_for_raw_pointer_reference_casts(_tokens: TokenStream) -> TokenStream {
    TokenStream::new()
}

#[cfg(not(feature = "prusti"))]
#[proc_macro]
pub fn join(_tokens: TokenStream) -> TokenStream {
    TokenStream::new()
}

#[cfg(not(feature = "prusti"))]
#[proc_macro]
pub fn join_range(_tokens: TokenStream) -> TokenStream {
    TokenStream::new()
}

#[cfg(not(feature = "prusti"))]
#[proc_macro]
pub fn split(_tokens: TokenStream) -> TokenStream {
    TokenStream::new()
}

#[cfg(not(feature = "prusti"))]
#[proc_macro]
pub fn split_range(_tokens: TokenStream) -> TokenStream {
    TokenStream::new()
}

#[cfg(not(feature = "prusti"))]
#[proc_macro]
pub fn stash_range(_tokens: TokenStream) -> TokenStream {
    TokenStream::new()
}

#[cfg(not(feature = "prusti"))]
#[proc_macro]
pub fn restore_stash_range(_tokens: TokenStream) -> TokenStream {
    TokenStream::new()
}

#[cfg(not(feature = "prusti"))]
#[proc_macro]
pub fn close_ref(_tokens: TokenStream) -> TokenStream {
    TokenStream::new()
}

#[cfg(not(feature = "prusti"))]
#[proc_macro]
pub fn open_ref(_tokens: TokenStream) -> TokenStream {
    TokenStream::new()
}

#[cfg(not(feature = "prusti"))]
#[proc_macro]
pub fn close_mut_ref(_tokens: TokenStream) -> TokenStream {
    TokenStream::new()
}

#[cfg(not(feature = "prusti"))]
#[proc_macro]
pub fn open_mut_ref(_tokens: TokenStream) -> TokenStream {
    TokenStream::new()
}

#[cfg(not(feature = "prusti"))]
#[proc_macro]
pub fn resolve(_tokens: TokenStream) -> TokenStream {
    TokenStream::new()
}

#[cfg(not(feature = "prusti"))]
#[proc_macro]
pub fn resolve_range(_tokens: TokenStream) -> TokenStream {
    TokenStream::new()
}

#[cfg(not(feature = "prusti"))]
#[proc_macro]
pub fn forget_initialization(_tokens: TokenStream) -> TokenStream {
    TokenStream::new()
}

#[cfg(not(feature = "prusti"))]
#[proc_macro]
pub fn forget_initialization_range(_tokens: TokenStream) -> TokenStream {
    TokenStream::new()
}

#[cfg(not(feature = "prusti"))]
#[proc_macro]
pub fn restore(_tokens: TokenStream) -> TokenStream {
    TokenStream::new()
}

#[cfg(not(feature = "prusti"))]
#[proc_macro]
pub fn set_union_active_field(_tokens: TokenStream) -> TokenStream {
    TokenStream::new()
}

// ----------------------
// --- PRUSTI ENABLED ---

#[cfg(feature = "prusti")]
use prusti_specs::{rewrite_prusti_attributes, SpecAttributeKind};

#[cfg(feature = "prusti")]
#[proc_macro_attribute]
pub fn requires(attr: TokenStream, tokens: TokenStream) -> TokenStream {
    rewrite_prusti_attributes(SpecAttributeKind::Requires, attr.into(), tokens.into()).into()
}

/// FIXME: Remove.
#[cfg(feature = "prusti")]
#[proc_macro_attribute]
pub fn not_require(attr: TokenStream, tokens: TokenStream) -> TokenStream {
    rewrite_prusti_attributes(SpecAttributeKind::NotRequire, attr.into(), tokens.into()).into()
}

#[cfg(feature = "prusti")]
#[proc_macro_attribute]
pub fn ensures(attr: TokenStream, tokens: TokenStream) -> TokenStream {
    rewrite_prusti_attributes(SpecAttributeKind::Ensures, attr.into(), tokens.into()).into()
}

/// FIXME: Remove.
#[cfg(feature = "prusti")]
#[proc_macro_attribute]
pub fn not_ensure(attr: TokenStream, tokens: TokenStream) -> TokenStream {
    rewrite_prusti_attributes(SpecAttributeKind::NotEnsure, attr.into(), tokens.into()).into()
}

/// FIXME: Cleanup.
#[cfg(feature = "prusti")]
#[proc_macro_attribute]
pub fn broken_invariant(attr: TokenStream, tokens: TokenStream) -> TokenStream {
    rewrite_prusti_attributes(SpecAttributeKind::NotRequire, attr.into(), tokens.into()).into()
}

#[cfg(feature = "prusti")]
#[proc_macro_attribute]
pub fn after_expiry(attr: TokenStream, tokens: TokenStream) -> TokenStream {
    rewrite_prusti_attributes(SpecAttributeKind::AfterExpiry, attr.into(), tokens.into()).into()
}

#[cfg(feature = "prusti")]
#[proc_macro_attribute]
pub fn assert_on_expiry(attr: TokenStream, tokens: TokenStream) -> TokenStream {
    rewrite_prusti_attributes(
        SpecAttributeKind::AssertOnExpiry,
        attr.into(),
        tokens.into(),
    )
    .into()
}

#[cfg(feature = "prusti")]
#[proc_macro_attribute]
pub fn pure(attr: TokenStream, tokens: TokenStream) -> TokenStream {
    rewrite_prusti_attributes(SpecAttributeKind::Pure, attr.into(), tokens.into()).into()
}

#[cfg(feature = "prusti")]
#[proc_macro_attribute]
pub fn trusted(attr: TokenStream, tokens: TokenStream) -> TokenStream {
    prusti_specs::trusted(attr.into(), tokens.into()).into()
}

#[cfg(feature = "prusti")]
#[proc_macro_attribute]
pub fn verified(attr: TokenStream, tokens: TokenStream) -> TokenStream {
    rewrite_prusti_attributes(SpecAttributeKind::Verified, attr.into(), tokens.into()).into()
}

#[cfg(feature = "prusti")]
#[proc_macro_attribute]
pub fn no_panic(attr: TokenStream, tokens: TokenStream) -> TokenStream {
    rewrite_prusti_attributes(SpecAttributeKind::NoPanic, attr.into(), tokens.into()).into()
}

#[cfg(feature = "prusti")]
#[proc_macro_attribute]
pub fn no_panic_ensures_postcondition(attr: TokenStream, tokens: TokenStream) -> TokenStream {
    rewrite_prusti_attributes(
        SpecAttributeKind::NoPanicEnsuresPostcondition,
        attr.into(),
        tokens.into(),
    )
    .into()
}

#[cfg(feature = "prusti")]
#[proc_macro]
pub fn body_invariant(tokens: TokenStream) -> TokenStream {
    prusti_specs::body_invariant(tokens.into()).into()
}

#[cfg(feature = "prusti")]
#[proc_macro]
pub fn prusti_assert(tokens: TokenStream) -> TokenStream {
    prusti_specs::prusti_assertion(tokens.into()).into()
}

#[cfg(feature = "prusti")]
#[proc_macro]
pub fn prusti_structural_assert(tokens: TokenStream) -> TokenStream {
    prusti_specs::prusti_structural_assert(tokens.into()).into()
}

#[cfg(feature = "prusti")]
#[proc_macro]
pub fn prusti_assume(tokens: TokenStream) -> TokenStream {
    prusti_specs::prusti_assume(tokens.into()).into()
}

#[cfg(feature = "prusti")]
#[proc_macro]
pub fn prusti_refute(tokens: TokenStream) -> TokenStream {
    prusti_specs::prusti_refutation(tokens.into()).into()
}

#[cfg(feature = "prusti")]
#[proc_macro]
pub fn prusti_structural_assume(tokens: TokenStream) -> TokenStream {
    prusti_specs::prusti_structural_assume(tokens.into()).into()
}

#[cfg(feature = "prusti")]
#[proc_macro]
pub fn materialize_predicate(tokens: TokenStream) -> TokenStream {
    prusti_specs::materialize_predicate(tokens.into()).into()
}

#[cfg(feature = "prusti")]
#[proc_macro]
pub fn quantified_predicate(tokens: TokenStream) -> TokenStream {
    prusti_specs::quantified_predicate(tokens.into()).into()
}

#[cfg(feature = "prusti")]
#[proc_macro]
pub fn closure(tokens: TokenStream) -> TokenStream {
    prusti_specs::closure(tokens.into()).into()
}

#[cfg(feature = "prusti")]
#[proc_macro_attribute]
pub fn refine_trait_spec(attr: TokenStream, tokens: TokenStream) -> TokenStream {
    prusti_specs::refine_trait_spec(attr.into(), tokens.into()).into()
}

#[cfg(feature = "prusti")]
#[proc_macro_attribute]
pub fn extern_spec(attr: TokenStream, tokens: TokenStream) -> TokenStream {
    prusti_specs::extern_spec(attr.into(), tokens.into()).into()
}

#[cfg(feature = "prusti")]
#[proc_macro_attribute]
pub fn invariant(attr: TokenStream, tokens: TokenStream) -> TokenStream {
    prusti_specs::invariant(attr.into(), tokens.into(), false).into()
}

#[cfg(feature = "prusti")]
#[proc_macro_attribute]
pub fn structural_invariant(attr: TokenStream, tokens: TokenStream) -> TokenStream {
    prusti_specs::invariant(attr.into(), tokens.into(), true).into()
}

#[cfg(feature = "prusti")]
#[proc_macro]
pub fn predicate(tokens: TokenStream) -> TokenStream {
    prusti_specs::predicate(tokens.into()).into()
}

#[cfg(feature = "prusti")]
#[proc_macro_attribute]
pub fn model(_attr: TokenStream, tokens: TokenStream) -> TokenStream {
    prusti_specs::type_model(_attr.into(), tokens.into()).into()
}

#[cfg(feature = "prusti")]
#[proc_macro_attribute]
pub fn refine_spec(attr: TokenStream, tokens: TokenStream) -> TokenStream {
    rewrite_prusti_attributes(SpecAttributeKind::RefineSpec, attr.into(), tokens.into()).into()
}

#[cfg(feature = "prusti")]
#[proc_macro]
pub fn ghost(tokens: TokenStream) -> TokenStream {
    prusti_specs::ghost(tokens.into()).into()
}

#[cfg(feature = "prusti")]
#[proc_macro]
pub fn on_drop_unwind(tokens: TokenStream) -> TokenStream {
    prusti_specs::on_drop_unwind(tokens.into()).into()
}

#[cfg(feature = "prusti")]
#[proc_macro]
pub fn with_finally(tokens: TokenStream) -> TokenStream {
    prusti_specs::with_finally(tokens.into()).into()
}

#[cfg(feature = "prusti")]
#[proc_macro]
pub fn checked(tokens: TokenStream) -> TokenStream {
    prusti_specs::checked(tokens.into()).into()
}

#[cfg(feature = "prusti")]
#[proc_macro_attribute]
pub fn print_counterexample(attr: TokenStream, tokens: TokenStream) -> TokenStream {
    prusti_specs::print_counterexample(attr.into(), tokens.into()).into()
}

#[cfg(feature = "prusti")]
#[proc_macro_attribute]
pub fn terminates(attr: TokenStream, tokens: TokenStream) -> TokenStream {
    rewrite_prusti_attributes(SpecAttributeKind::Terminates, attr.into(), tokens.into()).into()
}

#[cfg(feature = "prusti")]
#[proc_macro]
pub fn body_variant(tokens: TokenStream) -> TokenStream {
    prusti_specs::body_variant(tokens.into()).into()
}

#[cfg(feature = "prusti")]
#[proc_macro]
pub fn manually_manage(tokens: TokenStream) -> TokenStream {
    prusti_specs::manually_manage(tokens.into()).into()
}

#[cfg(feature = "prusti")]
#[proc_macro]
pub fn pack(tokens: TokenStream) -> TokenStream {
    prusti_specs::pack(tokens.into()).into()
}

#[cfg(feature = "prusti")]
#[proc_macro]
pub fn unpack(tokens: TokenStream) -> TokenStream {
    prusti_specs::unpack(tokens.into()).into()
}

#[cfg(feature = "prusti")]
#[proc_macro]
pub fn obtain(tokens: TokenStream) -> TokenStream {
    prusti_specs::obtain(tokens.into()).into()
}

#[cfg(feature = "prusti")]
#[proc_macro]
pub fn pack_ref(tokens: TokenStream) -> TokenStream {
    prusti_specs::pack_ref(tokens.into()).into()
}

#[cfg(feature = "prusti")]
#[proc_macro]
pub fn unpack_ref(tokens: TokenStream) -> TokenStream {
    prusti_specs::unpack_ref(tokens.into()).into()
}

#[cfg(feature = "prusti")]
#[proc_macro]
pub fn pack_mut_ref(tokens: TokenStream) -> TokenStream {
    prusti_specs::pack_mut_ref(tokens.into()).into()
}

#[cfg(feature = "prusti")]
#[proc_macro]
pub fn unpack_mut_ref(tokens: TokenStream) -> TokenStream {
    prusti_specs::unpack_mut_ref(tokens.into()).into()
}

#[cfg(feature = "prusti")]
#[proc_macro]
pub fn take_lifetime(tokens: TokenStream) -> TokenStream {
    prusti_specs::take_lifetime(tokens.into()).into()
}

#[cfg(feature = "prusti")]
#[proc_macro]
pub fn set_lifetime_for_raw_pointer_reference_casts(tokens: TokenStream) -> TokenStream {
    prusti_specs::set_lifetime_for_raw_pointer_reference_casts(tokens.into()).into()
}

#[cfg(feature = "prusti")]
#[proc_macro]
pub fn join(tokens: TokenStream) -> TokenStream {
    prusti_specs::join(tokens.into()).into()
}

#[cfg(feature = "prusti")]
#[proc_macro]
pub fn join_range(tokens: TokenStream) -> TokenStream {
    prusti_specs::join_range(tokens.into()).into()
}

#[cfg(feature = "prusti")]
#[proc_macro]
pub fn split(tokens: TokenStream) -> TokenStream {
    prusti_specs::split(tokens.into()).into()
}

#[cfg(feature = "prusti")]
#[proc_macro]
pub fn split_range(tokens: TokenStream) -> TokenStream {
    prusti_specs::split_range(tokens.into()).into()
}

#[cfg(feature = "prusti")]
#[proc_macro]
pub fn stash_range(tokens: TokenStream) -> TokenStream {
    prusti_specs::stash_range(tokens.into()).into()
}

#[cfg(feature = "prusti")]
#[proc_macro]
pub fn restore_stash_range(tokens: TokenStream) -> TokenStream {
    prusti_specs::restore_stash_range(tokens.into()).into()
}

#[cfg(feature = "prusti")]
#[proc_macro]
pub fn close_ref(tokens: TokenStream) -> TokenStream {
    prusti_specs::close_ref(tokens.into()).into()
}

#[cfg(feature = "prusti")]
#[proc_macro]
pub fn open_ref(tokens: TokenStream) -> TokenStream {
    prusti_specs::open_ref(tokens.into()).into()
}

#[cfg(feature = "prusti")]
#[proc_macro]
pub fn close_mut_ref(tokens: TokenStream) -> TokenStream {
    prusti_specs::close_mut_ref(tokens.into()).into()
}

#[cfg(feature = "prusti")]
#[proc_macro]
pub fn open_mut_ref(tokens: TokenStream) -> TokenStream {
    prusti_specs::open_mut_ref(tokens.into()).into()
}

#[cfg(feature = "prusti")]
#[proc_macro]
pub fn resolve(tokens: TokenStream) -> TokenStream {
    prusti_specs::resolve(tokens.into()).into()
}

#[cfg(feature = "prusti")]
#[proc_macro]
pub fn resolve_range(tokens: TokenStream) -> TokenStream {
    prusti_specs::resolve_range(tokens.into()).into()
}

#[cfg(feature = "prusti")]
#[proc_macro]
pub fn forget_initialization(tokens: TokenStream) -> TokenStream {
    prusti_specs::forget_initialization(tokens.into()).into()
}

#[cfg(feature = "prusti")]
#[proc_macro]
pub fn forget_initialization_range(tokens: TokenStream) -> TokenStream {
    prusti_specs::forget_initialization_range(tokens.into()).into()
}

#[cfg(feature = "prusti")]
#[proc_macro]
pub fn restore(tokens: TokenStream) -> TokenStream {
    prusti_specs::restore(tokens.into()).into()
}

#[cfg(feature = "prusti")]
#[proc_macro]
pub fn set_union_active_field(tokens: TokenStream) -> TokenStream {
    prusti_specs::set_union_active_field(tokens.into()).into()
}

// Ensure that you've also crated a transparent `#[cfg(not(feature = "prusti"))]`
// version of your new macro above!
