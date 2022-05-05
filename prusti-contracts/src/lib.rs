#![no_std]
#![feature(register_tool)]
#![register_tool(prusti)]
#![feature(decl_macro)]

#[cfg(not(feature = "prusti"))]
mod private {
    /// A macro for writing a precondition on a function.
    pub use prusti_contracts_impl::requires;

    /// A macro for writing a postcondition on a function.
    pub use prusti_contracts_impl::ensures;

    /// A macro for writing a pledge on a function.
    pub use prusti_contracts_impl::after_expiry;

    /// A macro for writing a two-state pledge on a function.
    pub use prusti_contracts_impl::assert_on_expiry;

    /// A macro for marking a function as pure.
    pub use prusti_contracts_impl::pure;

    /// A macro for marking a function as trusted.
    pub use prusti_contracts_impl::trusted;

    /// A macro for writing a loop body invariant.
    pub use prusti_contracts_impl::body_invariant;

    /// A macro for defining a closure with a specification.
    /// Note: this is a declarative macro defined in this crate
    /// because declarative macros can't be exported from
    /// the `prusti-contracts-impl` proc-macro crate.
    /// See <https://github.com/rust-lang/rust/issues/40090>.
    #[macro_export]
    macro_rules! closure {
        ($condition:ident ($($args:tt)*), $($tail:tt)*) => {
            $crate::closure!($($tail)*)
        };
        ($($tail:tt)*) => {
            $($tail)*
        };
    }

    /// A macro for impl blocks that refine trait specifications.
    pub use prusti_contracts_impl::refine_trait_spec;

    /// A macro for specifying external functions.
    pub use prusti_contracts_impl::extern_spec;

    /// A macro for defining a predicate using prusti expression syntax instead
    /// of just Rust expressions.
    pub use prusti_contracts_impl::predicate;

    /// Macro for creating type models.
    pub use prusti_contracts_impl::model;

    /// A macro to add trait bounds on a generic type parameter and specifications
    /// which are active only when these bounds are satisfied for a call.
    pub use prusti_contracts_impl::ghost_constraint;

    /// A sequence type
    #[non_exhaustive]
    #[derive(PartialEq, Eq, Copy, Clone)]
    pub struct Seq<T> {
        _phantom: core::marker::PhantomData<T>,
    }

    /// A macro for defining ghost blocks which will be left in for verification
    /// but omitted during compilation.
    pub use prusti_contracts_impl::ghost;

    /// a mathematical (unbounded) integer type
    /// it should not be constructed from running rust code, hence the private unit inside
    pub struct Int(());
}

#[cfg(feature = "prusti")]
mod private {
    /// A macro for writing a precondition on a function.
    pub use prusti_contracts_internal::requires;

    /// A macro for writing a postcondition on a function.
    pub use prusti_contracts_internal::ensures;

    /// A macro for writing a pledge on a function.
    pub use prusti_contracts_internal::after_expiry;

    /// A macro for writing a two-state pledge on a function.
    pub use prusti_contracts_internal::assert_on_expiry;

    /// A macro for marking a function as pure.
    pub use prusti_contracts_internal::pure;

    /// A macro for marking a function as trusted.
    pub use prusti_contracts_internal::trusted;

    /// A macro for writing a loop body invariant.
    pub use prusti_contracts_internal::body_invariant;

    /// A macro for defining a closure with a specification.
    pub use prusti_contracts_internal::closure;

    /// A macro for impl blocks that refine trait specifications.
    pub use prusti_contracts_internal::refine_trait_spec;

    /// A macro for specifying external functions.
    pub use prusti_contracts_internal::extern_spec;

    /// A macro for defining a predicate using prusti expression syntax instead
    /// of just Rust expressions.
    pub use prusti_contracts_internal::predicate;

    /// Macro for creating type models.
    pub use prusti_contracts_internal::model;

    /// A macro to add trait bounds on a generic type parameter and specifications
    /// which are active only when these bounds are satisfied for a call.
    pub use prusti_contracts_internal::ghost_constraint;

    pub fn prusti_set_union_active_field<T>(_arg: T) {
        unreachable!();
    }

    /// a mathematical (unbounded) integer type
    /// it should not be constructed from running rust code, hence the private unit inside
    #[derive(PartialEq, Eq, Copy, Clone)]
    pub struct Int(());

    impl Int {
        #[pure]
        pub fn new(_: i64) -> Self {
            panic!()
        }
    }

    /// A sequence type
    #[non_exhaustive]
    #[derive(PartialEq, Eq, Copy, Clone)]
    pub struct Seq<T: Copy> {
        _phantom: core::marker::PhantomData<T>,
    }

    impl<T: Copy> Seq<T> {
        #[pure]
        pub fn empty() -> Self {
            panic!()
        }
        #[pure]
        pub fn single(_: T) -> Self {
            panic!()
        }
        #[pure]
        pub fn concat(_: Self, _: Self) -> Self {
            panic!()
        }
        #[pure]
        pub fn lookup(self, _index: usize) -> T {
            panic!()
        }
        #[pure]
        pub fn len(self) -> Int {
            panic!()
        }
    }

    /// A map type
    #[non_exhaustive]
    #[derive(PartialEq, Eq, Copy, Clone)]
    pub struct Map<K, V> {
        _key_phantom: core::marker::PhantomData<K>,
        _val_phantom: core::marker::PhantomData<V>,
    }

    impl<K, V> Map<K, V> {
        #[pure]
        pub fn empty() -> Self {
            panic!()
        }
        #[pure]
        pub fn insert(self, _key: K, _val: V) -> Self {
            panic!()
        }
        #[pure]
        pub fn delete(self, _key: K) -> Self {
            panic!()
        }
        #[pure]
        pub fn len(self) -> Int {
            panic!()
        }
        #[pure]
        pub fn lookup(self, _key: K) -> V {
            panic!()
        }
    }

    /// A macro for defining ghost blocks which will be left in for verification
    /// but omitted during compilation.
    pub use prusti_contracts_internal::ghost;
}

/// This function is used to evaluate an expression in the context just
/// before the borrows expires.
pub fn before_expiry<T>(arg: T) -> T {
    arg
}

/// This function is used to evaluate an expression in the “old”
/// context, that is at the beginning of the method call.
pub fn old<T>(arg: T) -> T {
    arg
}

pub fn forall<T, F>(_trigger_set: T, _closure: F) -> bool {
    true
}

pub fn exists<T, F>(_trigger_set: T, _closure: F) -> bool {
    true
}

pub use private::*;
