#![no_std]

/// A macro for writing a precondition on a function.
pub use prusti_contracts_proc_macros::requires;

/// A macro for writing a postcondition on a function.
pub use prusti_contracts_proc_macros::ensures;

/// A macro for writing a pledge on a function.
pub use prusti_contracts_proc_macros::after_expiry;

/// A macro for writing a two-state pledge on a function.
pub use prusti_contracts_proc_macros::assert_on_expiry;

/// A macro for marking a function as pure.
pub use prusti_contracts_proc_macros::pure;

/// A macro for marking a function as trusted.
pub use prusti_contracts_proc_macros::trusted;

/// A macro for type invariants.
pub use prusti_contracts_proc_macros::invariant;

/// A macro for structural type invariants. A type with a structural
/// invariant needs to be managed manually by the user.
pub use prusti_contracts_proc_macros::structural_invariant;

/// A macro for writing a loop body invariant.
pub use prusti_contracts_proc_macros::body_invariant;

/// A macro for writing assertions using the full prusti specifications
pub use prusti_contracts_proc_macros::prusti_assert;

/// A macro for writing assumptions using prusti syntax
pub use prusti_contracts_proc_macros::prusti_assume;

/// A macro for impl blocks that refine trait specifications.
pub use prusti_contracts_proc_macros::refine_trait_spec;

/// A macro for specifying external functions.
pub use prusti_contracts_proc_macros::extern_spec;

/// A macro for defining a predicate using prusti expression syntax instead
/// of just Rust expressions.
pub use prusti_contracts_proc_macros::predicate;

/// Macro for creating type models.
pub use prusti_contracts_proc_macros::model;

/// A macro to add trait bounds on a generic type parameter and specifications
/// which are active only when these bounds are satisfied for a call.
pub use prusti_contracts_proc_macros::ghost_constraint;

/// A macro for defining ghost blocks which will be left in for verification
/// but omitted during compilation.
pub use prusti_contracts_proc_macros::ghost;

/// A macro to customize how a struct or enum should be printed in a counterexample
pub use prusti_contracts_proc_macros::print_counterexample;

/// A macro to annotate termination of a function
pub use prusti_contracts_proc_macros::terminates;

/// A macro to annotate body variant of a loop to prove termination
pub use prusti_contracts_proc_macros::body_variant;

/// A macro to mark the place as manually managed.
pub use prusti_contracts_proc_macros::manually_manage;

/// A macro to manually pack a place capability.
pub use prusti_contracts_proc_macros::pack;

/// A macro to manually unpack a place capability.
pub use prusti_contracts_proc_macros::unpack;

/// A macro to manually pack a place capability.
pub use prusti_contracts_proc_macros::pack_ref;

/// A macro to manually unpack a place capability.
pub use prusti_contracts_proc_macros::unpack_ref;

/// A macro to manually pack a place capability.
pub use prusti_contracts_proc_macros::pack_mut_ref;

/// A macro to manually unpack a place capability.
pub use prusti_contracts_proc_macros::unpack_mut_ref;

/// A macro to obtain a lifetime of a variable.
pub use prusti_contracts_proc_macros::take_lifetime;

/// A macro to manually join a place capability.
pub use prusti_contracts_proc_macros::join;

/// A macro to manually join a range of memory blocks into one.
pub use prusti_contracts_proc_macros::join_range;

/// A macro to manually split a place capability.
pub use prusti_contracts_proc_macros::split;

/// A macro to manually split a memory block into a range of memory blocks.
pub use prusti_contracts_proc_macros::split_range;

/// A macro to stash away a range of own capabilities to get access to
/// underlying raw memory.
pub use prusti_contracts_proc_macros::stash_range;

/// A macro to restore the stash away a range of own capabilities.
pub use prusti_contracts_proc_macros::restore_stash_range;

/// A macro to manually close a reference.
pub use prusti_contracts_proc_macros::close_ref;

/// A macro to manually open a reference.
pub use prusti_contracts_proc_macros::open_ref;

/// A macro to manually close a reference.
pub use prusti_contracts_proc_macros::close_mut_ref;

/// A macro to manually open a reference.
pub use prusti_contracts_proc_macros::open_mut_ref;

/// A macro to forget that a place is initialized.
pub use prusti_contracts_proc_macros::forget_initialization;

/// A macro to restore a place capability.
pub use prusti_contracts_proc_macros::restore;

/// A macro to set a specific field of the union as active.
pub use prusti_contracts_proc_macros::set_union_active_field;

#[cfg(not(feature = "prusti"))]
mod private {
    use core::marker::PhantomData;

    /// A macro for defining a closure with a specification.
    /// Note: this is a declarative macro defined in this crate
    /// because declarative macros can't be exported from
    /// the `prusti-contracts-proc-macros` proc-macro crate.
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

    /// a mathematical (unbounded) integer type
    /// it should not be constructed from running rust code, hence the private unit inside
    pub struct Int(());

    #[non_exhaustive]
    #[derive(PartialEq, Eq, Copy, Clone)]
    pub struct Ghost<T> {
        _phantom: PhantomData<T>,
    }

    /// A type allowing to refer to a lifetime in places where Rust syntax does
    /// not allow it. It should not be possible to construct from Rust code,
    /// hence the private unit inside.
    pub struct Lifetime(());
}

#[cfg(feature = "prusti")]
pub mod core_spec;

#[cfg(feature = "prusti")]
mod private {
    use core::{marker::PhantomData, ops::*};

    /// A macro for defining a closure with a specification.
    pub use prusti_contracts_proc_macros::{closure, pure, trusted};

    // pub fn prusti_set_union_active_field<T>(_arg: T) {
    //     unreachable!();
    // }

    #[pure]
    pub fn prusti_terminates_trusted() -> Int {
        Int::new(1)
    }

    /// A type allowing to refer to a lifetime in places where Rust syntax does
    /// not allow it. It should not be possible to construct from Rust code,
    /// hence the private unit inside.
    #[derive(Copy, Clone)]
    pub struct Lifetime(());

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

/// Universal quantifier.
///
/// This is a Prusti-internal representation of the `forall` syntax.
pub fn forall<T, F>(_trigger_set: T, _closure: F) -> bool {
    true
}

/// Existential quantifier.
///
/// This is a Prusti-internal representation of the `exists` syntax.
pub fn exists<T, F>(_trigger_set: T, _closure: F) -> bool {
    true
}

/// Creates an owned copy of a reference. This should only be used from within
/// ghost code, as it circumvents the borrow checker.
pub fn snap<T>(_x: &T) -> T {
    unimplemented!()
}

/// Snapshot, "logical", or "mathematical" equality. Compares the in-memory
/// representation of two instances of the same type, even if there is no
/// `PartialEq` nor `Copy` implementation. The in-memory representation is
/// constructed recursively: references are followed, unsafe pointers and cells
/// are not. Importantly, addresses are not taken into consideration.
pub fn snapshot_equality<T>(_l: T, _r: T) -> bool {
    true
}

#[doc(hidden)]
#[trusted]
pub fn prusti_manually_manage<T>(_arg: T) {
    unreachable!();
}

#[doc(hidden)]
#[trusted]
pub fn prusti_pack_place<T>(_arg: T) {
    unreachable!();
}

#[doc(hidden)]
#[trusted]
pub fn prusti_unpack_place<T>(_arg: T) {
    unreachable!();
}

#[doc(hidden)]
#[trusted]
pub fn prusti_pack_ref_place<T>(_lifetime_name: &'static str, _arg: T) {
    unreachable!();
}

#[doc(hidden)]
#[trusted]
pub fn prusti_unpack_ref_place<T>(_lifetime_name: &'static str, _arg: T) {
    unreachable!();
}

#[doc(hidden)]
#[trusted]
pub fn prusti_pack__mut_ref_place<T>(_lifetime_name: &'static str, _arg: T) {
    unreachable!();
}

#[doc(hidden)]
#[trusted]
pub fn prusti_unpack_mut_ref_place<T>(_lifetime_name: &'static str, _arg: T) {
    unreachable!();
}

#[doc(hidden)]
#[trusted]
pub fn prusti_take_lifetime<T>(_arg: T, _lifetime_name: &'static str) -> Lifetime {
    unreachable!();
}

#[doc(hidden)]
#[trusted]
pub fn prusti_join_place<T>(_arg: T) {
    unreachable!();
}

#[doc(hidden)]
#[trusted]
pub fn prusti_join_range<T>(_arg: T, _start_index: usize, _end_index: usize) {
    unreachable!();
}

#[doc(hidden)]
#[trusted]
pub fn prusti_split_place<T>(_arg: T) {
    unreachable!();
}

#[doc(hidden)]
#[trusted]
pub fn prusti_split_range<T>(_arg: T, _start_index: usize, _end_index: usize) {
    unreachable!();
}

#[doc(hidden)]
#[trusted]
pub fn prusti_stash_range<T>(
    _arg: T,
    _start_index: usize,
    _end_index: usize,
    _witness: &'static str,
) {
    unreachable!();
}

#[doc(hidden)]
#[trusted]
pub fn prusti_restore_stash_range<T>(_arg: T, _new_start_index: usize, _witness: &'static str) {
    unreachable!();
}

#[doc(hidden)]
#[trusted]
pub fn prusti_close_ref_place(_witness: &'static str) {
    unreachable!();
}

#[doc(hidden)]
#[trusted]
pub fn prusti_open_ref_place<T>(_lifetime: &'static str, _arg: T, _witness: &'static str) {
    unreachable!();
}

#[doc(hidden)]
#[trusted]
pub fn prusti_close_mut_ref_place(_witness: &'static str) {
    unreachable!();
}

#[doc(hidden)]
#[trusted]
pub fn prusti_open_mut_ref_place<T>(_lifetime: &'static str, _arg: T, _witness: &'static str) {
    unreachable!();
}

#[doc(hidden)]
#[trusted]
pub fn prusti_forget_initialization<T>(_arg: T) {
    unreachable!();
}

#[doc(hidden)]
#[trusted]
pub fn prusti_restore_place<T>(_arg1: T, _arg2: T) {
    unreachable!();
}

#[doc(hidden)]
#[trusted]
pub fn prusti_set_union_active_field<T>(_arg: T) {
    unreachable!();
}

/// Indicates that we have the `own` capability to the specified place.
#[doc(hidden)]
#[trusted]
pub fn prusti_own<T>(_place: T) -> bool {
    unreachable!();
}

#[macro_export]
macro_rules! own {
    ($place:expr) => {
        $crate::prusti_own(unsafe { core::ptr::addr_of!($place) })
    };
}

/// Indicates that we have the `own` capability to the specified range.
#[doc(hidden)]
#[trusted]
pub fn prusti_own_range<T>(_address: T, _start: usize, _end: usize) -> bool {
    unreachable!();
}

#[macro_export]
macro_rules! own_range {
    ($address:expr, $start:expr, $end:expr) => {
        $crate::prusti_own_range(unsafe { core::ptr::addr_of!($address) }, $start, $end)
    };
}

/// Indicates that we have the `raw` capability to the specified address.
#[doc(hidden)]
#[trusted]
pub fn prusti_raw<T>(_address: T, _size: usize) -> bool {
    true
}

#[macro_export]
macro_rules! raw {
    ($place:expr, $size: expr) => {
        $crate::prusti_raw(unsafe { core::ptr::addr_of!($place) }, $size)
    };
}

/// Indicates that we have the `raw` capability to the specified range.
#[doc(hidden)]
#[trusted]
pub fn prusti_raw_range<T>(_address: T, _size: usize, _start: usize, _end: usize) -> bool {
    unreachable!();
}

#[macro_export]
macro_rules! raw_range {
    ($address:expr, $size:expr, $start:expr, $end:expr) => {
        $crate::prusti_raw_range(
            unsafe { core::ptr::addr_of!($address) },
            $size,
            $start,
            $end,
        )
    };
}

/// Indicates that we have the capability to deallocate.
#[doc(hidden)]
#[trusted]
pub fn prusti_raw_dealloc<T>(_address: T, _size: usize) -> bool {
    true
}

#[macro_export]
macro_rules! raw_dealloc {
    ($place:expr, $size: expr, $align: expr) => {
        $crate::prusti_raw_dealloc(unsafe { core::ptr::addr_of!($place) }, $size)
    };
}

/// Temporarily unpacks the owned predicate at the given location.
#[doc(hidden)]
#[trusted]
pub fn prusti_unpacking<T, U>(_place: T, _body: U) -> U {
    unimplemented!()
}

#[macro_export]
macro_rules! unpacking {
    ($place:expr, $body: expr) => {
        $crate::prusti_unpacking(unsafe { core::ptr::addr_of!($place) }, $body)
    };
}

pub use private::*;
