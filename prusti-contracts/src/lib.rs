#![no_std]

#[cfg(not(feature = "prusti"))]
mod private {
    use core::marker::PhantomData;

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

    /// A macro for type invariants.
    pub use prusti_contracts_impl::invariant;

    /// A macro for writing a loop body invariant.
    pub use prusti_contracts_impl::body_invariant;

    /// A macro for writing assertions using the full prusti specifications
    pub use prusti_contracts_impl::prusti_assert;

    /// A macro for writing assumptions using prusti syntax
    pub use prusti_contracts_impl::prusti_assume;

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
        _phantom: PhantomData<T>,
    }

    /// A map type
    #[non_exhaustive]
    #[derive(PartialEq, Eq, Copy, Clone)]
    pub struct Map<K, V> {
        _key_phantom: PhantomData<K>,
        _val_phantom: PhantomData<V>,
    }

    /// A macro for defining ghost blocks which will be left in for verification
    /// but omitted during compilation.
    pub use prusti_contracts_impl::ghost;

    /// a mathematical (unbounded) integer type
    /// it should not be constructed from running rust code, hence the private unit inside
    pub struct Int(());

    #[non_exhaustive]
    #[derive(PartialEq, Eq, Copy, Clone)]
    pub struct Ghost<T> {
        _phantom: PhantomData<T>,
    }
}

#[cfg(feature = "prusti")]
mod private {
    use core::{marker::PhantomData, ops::*};

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

    /// A macro for type invariants.
    pub use prusti_contracts_internal::invariant;

    /// A macro for writing a loop body invariant.
    pub use prusti_contracts_internal::body_invariant;

    /// A macro for writing assertions using the full prusti specifications
    pub use prusti_contracts_internal::prusti_assert;

    /// A macro for writing assumptions using prusti syntax
    pub use prusti_contracts_internal::prusti_assume;

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
    #[derive(Copy, Clone, PartialEq, Eq)]
    pub struct Int(());

    impl Int {
        pub fn new(_: i64) -> Self {
            panic!()
        }

        pub fn new_usize(_: usize) -> Self {
            panic!()
        }
    }

    macro_rules! __int_dummy_trait_impls__ {
        ($($trait:ident $fun:ident),*) => {$(
            impl core::ops::$trait for Int {
                type Output = Self;
                fn $fun(self, _other: Self) -> Self {
                    panic!()
                }
            }
        )*}
    }

    __int_dummy_trait_impls__!(Add add, Sub sub, Mul mul, Div div, Rem rem);

    impl Neg for Int {
        type Output = Self;
        fn neg(self) -> Self {
            panic!()
        }
    }

    impl PartialOrd for Int {
        fn partial_cmp(&self, _other: &Self) -> Option<core::cmp::Ordering> {
            panic!()
        }
    }
    impl Ord for Int {
        fn cmp(&self, _other: &Self) -> core::cmp::Ordering {
            panic!()
        }
    }

    /// A sequence type
    #[non_exhaustive]
    #[derive(PartialEq, Eq, Copy, Clone)]
    pub struct Seq<T: Copy> {
        _phantom: PhantomData<T>,
    }

    impl<T: Copy> Seq<T> {
        pub fn empty() -> Self {
            panic!()
        }
        pub fn single(_: T) -> Self {
            panic!()
        }
        pub fn concat(self, _: Self) -> Self {
            panic!()
        }
        pub fn lookup(self, _index: usize) -> T {
            panic!()
        }
        pub fn len(self) -> Int {
            panic!()
        }
    }

    #[macro_export]
    macro_rules! seq {
        ($val:expr) => {
            $crate::Seq::single($val)
        };
        ($($val:expr),*) => {
            $crate::Seq::empty()
            $(
                .concat(seq![$val])
            )*
        };
    }

    impl<T: Copy> Index<usize> for Seq<T> {
        type Output = T;
        fn index(&self, _: usize) -> &T {
            panic!()
        }
    }

    impl<T: Copy> Index<Int> for Seq<T> {
        type Output = T;
        fn index(&self, _: Int) -> &T {
            panic!()
        }
    }

    /// A map type
    #[non_exhaustive]
    #[derive(PartialEq, Eq, Copy, Clone)]
    pub struct Map<K, V> {
        _key_phantom: PhantomData<K>,
        _val_phantom: PhantomData<V>,
    }

    impl<K, V> Map<K, V> {
        pub fn empty() -> Self {
            panic!()
        }
        pub fn insert(self, _key: K, _val: V) -> Self {
            panic!()
        }
        pub fn delete(self, _key: K) -> Self {
            panic!()
        }
        pub fn len(self) -> Int {
            panic!()
        }
        pub fn lookup(self, _key: K) -> V {
            panic!()
        }
        pub fn contains(self, _key: K) -> bool {
            panic!()
        }
    }

    #[macro_export]
    macro_rules! map {
        ($($key:expr => $val:expr),*) => {
            map!($crate::Map::empty(), $($key => $val),*)
        };
        ($existing_map:expr, $($key:expr => $val:expr),*) => {
            $existing_map
            $(
                .insert($key, $val)
            )*
        };
    }

    impl<K, V> core::ops::Index<K> for Map<K, V> {
        type Output = V;
        fn index(&self, _key: K) -> &V {
            panic!()
        }
    }

    #[non_exhaustive]
    #[derive(PartialEq, Eq, Copy, Clone)]
    pub struct Ghost<T> {
        _phantom: PhantomData<T>,
    }

    impl<T> Ghost<T> {
        pub fn new(_: T) -> Self {
            panic!()
        }
    }

    impl<T> Deref for Ghost<T> {
        type Target = T;
        fn deref(&self) -> &T {
            panic!()
        }
    }

    impl<T> DerefMut for Ghost<T> {
        fn deref_mut(&mut self) -> &mut T {
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
