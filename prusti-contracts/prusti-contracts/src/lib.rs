// #![no_std]  FIXME

/// A macro for writing a precondition on a function.
pub use prusti_contracts_proc_macros::requires;

/// A macro to indicate that the type invariant is not required by the function.
/// FIXME: Remove
pub use prusti_contracts_proc_macros::not_require;

/// A macro for writing a postcondition on a function.
pub use prusti_contracts_proc_macros::ensures;

/// A macro to indicate that the type invariant is not ensured by the function.
/// FIXME: Remove
pub use prusti_contracts_proc_macros::not_ensure;

/// A macro to indicate that the type invariant is broken.
pub use prusti_contracts_proc_macros::broken_invariant;

/// A macro for writing a pledge on a function.
pub use prusti_contracts_proc_macros::after_expiry;

/// A macro for writing a two-state pledge on a function.
pub use prusti_contracts_proc_macros::assert_on_expiry;

/// A macro for marking a function as pure.
pub use prusti_contracts_proc_macros::pure;

/// A macro for marking a function as trusted.
pub use prusti_contracts_proc_macros::trusted;

/// A macro for marking that a function never panics.
pub use prusti_contracts_proc_macros::no_panic;

/// A macro for marking that if a function did not panic, then we can soundly
/// assume its postcondition even if the precondition did not hold. (This
/// basically means that we check the postcondition in memory safety mode.)
pub use prusti_contracts_proc_macros::no_panic_ensures_postcondition;

/// A macro for marking a function as opted into verification.
pub use prusti_contracts_proc_macros::verified;

/// A macro for type invariants.
pub use prusti_contracts_proc_macros::invariant;

/// A macro for structural type invariants. A type with a structural
/// invariant needs to be managed manually by the user.
pub use prusti_contracts_proc_macros::structural_invariant;

/// A macro for writing a loop body invariant.
pub use prusti_contracts_proc_macros::body_invariant;

/// A macro for writing assertions using the full prusti specifications
pub use prusti_contracts_proc_macros::prusti_assert;

/// A macro for writing structural assertions using prusti syntax
pub use prusti_contracts_proc_macros::prusti_structural_assert;

/// A macro for writing assumptions using prusti syntax
pub use prusti_contracts_proc_macros::prusti_assume;

/// A macro for writing structural assumptions using prusti syntax
pub use prusti_contracts_proc_macros::prusti_structural_assume;

/// A macro for telling Prusti purification to materialize a predicate instance.
pub use prusti_contracts_proc_macros::materialize_predicate;

/// A macro for telling Prusti purification that we have a predicate instance
/// coming from the quantifier.
pub use prusti_contracts_proc_macros::quantified_predicate;

/// A macro for writing refutations using prusti syntax
pub use prusti_contracts_proc_macros::prusti_refute;

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
pub use prusti_contracts_proc_macros::refine_spec;

/// A macro for defining ghost blocks which will be left in for verification
/// but omitted during compilation.
pub use prusti_contracts_proc_macros::ghost;

/// A macro for defining a ghost block that is executed when a specified place
/// is dropped.
pub use prusti_contracts_proc_macros::on_drop_unwind;

/// A macro for defining a ghost block that is executed when the execution
/// leaves the block including via panic.
pub use prusti_contracts_proc_macros::with_finally;

/// A macro that enables precondition checking when verifying in memory safety
/// mode.
pub use prusti_contracts_proc_macros::checked;

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

/// Tell Prusti to obtain the specified capability.
pub use prusti_contracts_proc_macros::obtain;

/// A macro to manually pack a place capability.
pub use prusti_contracts_proc_macros::pack_ref;

/// A macro to manually unpack a place capability.
pub use prusti_contracts_proc_macros::unpack_ref;

/// A macro to manually pack a place capability.
pub use prusti_contracts_proc_macros::pack_mut_ref;

/// A macro to manually unpack a place capability.
pub use prusti_contracts_proc_macros::unpack_mut_ref;

/// A macro to obtain a lifetime of a place.
pub use prusti_contracts_proc_macros::take_lifetime;

/// Set the lifetime of the place to be used for all raw pointer to reference
/// casts.
pub use prusti_contracts_proc_macros::set_lifetime_for_raw_pointer_reference_casts;

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

/// A macro to manually resolve a reference.
pub use prusti_contracts_proc_macros::resolve;

/// A macro to manually resolve a range of references.
pub use prusti_contracts_proc_macros::resolve_range;

/// A macro to forget that a place is initialized.
pub use prusti_contracts_proc_macros::forget_initialization;

/// A macro to forget that a range of places are initialized.
pub use prusti_contracts_proc_macros::forget_initialization_range;

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

    #[macro_export]
    macro_rules! prusti_assert_eq {
        ($left:expr, $right:expr $(,)?) => {};
    }

    #[macro_export]
    macro_rules! prusti_assert_ne {
        ($left:expr, $right:expr $(,)?) => {};
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

    /// A methematical type representing a machine byte.
    pub struct Byte(());

    /// A methematical type representing a sequence of machine bytes.
    pub struct Bytes(());
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

    #[macro_export]
    macro_rules! prusti_assert_eq {
        ($left:expr, $right:expr $(,)?) => {
            $crate::prusti_assert!($crate::snapshot_equality($left, $right))
        };
    }

    #[macro_export]
    macro_rules! prusti_assert_ne {
        ($left:expr, $right:expr $(,)?) => {
            $crate::prusti_assert!(!$crate::snapshot_equality($left, $right))
        };
    }

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

    /// A methematical type representing a machine byte.
    #[derive(Copy, Clone, PartialEq, Eq)]
    pub struct Byte(());

    /// A methematical type representing a sequence of machine bytes.
    #[derive(Copy, Clone, PartialEq, Eq)]
    pub struct Bytes(());
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
pub fn prusti_obtain_place<T>(_arg: T) {
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
pub fn prusti_pack_mut_ref_place<T>(_lifetime_name: &'static str, _arg: T) {
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
pub fn prusti_set_lifetime_for_raw_pointer_reference_casts<T>(_arg: T) {
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
/// We need to pass `_arg` to make sure the lifetime covers the closing of the
/// reference.
pub fn prusti_close_ref_place<T>(_arg: T, _witness: &'static str) {
    unreachable!();
}

#[doc(hidden)]
#[trusted]
pub fn prusti_open_ref_place<T>(_lifetime: &'static str, _arg: T, _witness: &'static str) {
    unreachable!();
}

#[doc(hidden)]
#[trusted]
/// We need to pass `_arg` to make sure the lifetime covers the closing of the
/// reference.
pub fn prusti_close_mut_ref_place<T>(_arg: T, _witness: &'static str) {
    unreachable!();
}

#[doc(hidden)]
#[trusted]
pub fn prusti_open_mut_ref_place<T>(_lifetime: &'static str, _arg: T, _witness: &'static str) {
    unreachable!();
}

#[doc(hidden)]
#[trusted]
pub fn prusti_resolve<T>(_arg: T) {
    unreachable!();
}

#[doc(hidden)]
#[trusted]
pub fn prusti_materialize_predicate<T>(_arg: T) {
    unreachable!();
}

#[doc(hidden)]
#[trusted]
pub fn prusti_quantified_predicate<T>(_arg: T) {
    unreachable!();
}

#[doc(hidden)]
#[trusted]
pub fn prusti_resolve_range<T>(
    _lifetime: &'static str,
    _arg: T,
    _predicate_range_start_index: usize,
    _predicate_range_end_index: usize,
    _start_index: usize,
    _end_index: usize,
) {
    unreachable!();
}

#[doc(hidden)]
#[trusted]
#[pure]
pub fn prusti_forget_initialization<T>(_arg: T) {
    unreachable!();
}

#[doc(hidden)]
#[trusted]
#[pure]
pub fn prusti_forget_initialization_range<T>(_address: T, _start: usize, _end: usize) {
    unreachable!();
}

#[doc(hidden)]
#[trusted]
pub fn prusti_on_drop_unwind<T>(_arg: T) {
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

/// Indicates that the expression should be evaluated assuming that the given
/// predicate is present.
#[doc(hidden)]
#[trusted]
pub fn prusti_eval_in<T>(_predicate: bool, _expression: T) -> T {
    unreachable!();
}

#[macro_export]
macro_rules! eval_in {
    ($predicate:expr, $expression:expr) => {
        $crate::prusti_eval_in($predicate, $expression)
    };
}

/// Indicates that the parameter's or return value invariant is broken.
#[doc(hidden)]
#[trusted]
#[pure]
pub fn prusti_broken_invariant<T>(_place: T) -> bool {
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
        $crate::prusti_own_range($address, $start, $end)
    };
}

/// Indicates that we have the shared reference capability to the specified
/// place.
#[doc(hidden)]
#[trusted]
pub fn prusti_shr<T>(_place: T) -> bool {
    unreachable!();
}

#[macro_export]
macro_rules! shr {
    ($place:expr) => {
        $crate::prusti_shr(unsafe { core::ptr::addr_of!($place) })
    };
}

/// Indicates that we have the unique reference capability to the specified
/// place.
#[doc(hidden)]
#[trusted]
pub fn prusti_unq<T1, T2>(_lifetime: T1, _place: T2) -> bool {
    unreachable!();
}

#[macro_export]
macro_rules! unq {
    ($lifetime:ident, $place:expr) => {
        $crate::prusti_unq(stringify!($lifetime), unsafe {
            core::ptr::addr_of!($place)
        })
    };
}

/// Deref a raw pointer with the specified offset.
#[doc(hidden)]
#[trusted]
pub unsafe fn prusti_deref_own<T>(_address: *const T, _index: usize) -> T {
    unreachable!();
}

#[macro_export]
macro_rules! deref_own {
    ($address:expr, $index:expr) => {
        unsafe { $crate::prusti_deref_own($address, $index) }
    };
}

/// Obtain the bytes of the specified memory block.
#[doc(hidden)]
#[trusted]
pub fn prusti_bytes<T>(_address: T, _length: usize) -> Bytes {
    unreachable!();
}

#[macro_export]
macro_rules! bytes {
    ($address:expr, $length:expr) => {
        $crate::prusti_bytes(unsafe { core::ptr::addr_of!($address) }, $length)
    };
}

/// Read the byte at the given index.
///
/// FIXME: This function does not check bounds. Instead, it returns garbage in
/// case of out-of-bounds
pub fn read_byte(_bytes: Bytes, _index: usize) -> Byte {
    unreachable!();
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
        $crate::prusti_raw_range($address, $size, $start, $end)
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

/// A ghost operation for computing an offset of the pointer.
pub fn address_offset_mut<T>(_ptr: *mut T, _count: isize) -> *mut T {
    unreachable!();
}

/// A ghost operation for computing an offset of the pointer.
pub fn address_offset<T>(_ptr: *const T, _count: isize) -> *const T {
    unreachable!();
}

#[trusted]
#[pure]
#[no_panic]
#[no_panic_ensures_postcondition]
pub fn allocation_never_fails() -> bool {
    unreachable!();
}

pub use private::*;
