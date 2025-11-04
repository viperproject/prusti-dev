use sealed::sealed;
use std::hash::Hash;

use serde::{Deserialize, Serialize};

use crate::{Type, TypeKind};

/// A compile-time known type (category).
#[sealed]
pub trait CompType:
    'static
    + Clone
    + Copy
    + core::fmt::Debug
    + PartialEq
    + Eq
    + PartialOrd
    + Ord
    + Hash
    + Serialize
    + for<'de> Deserialize<'de>
{
    fn check(ty: Type<impl CompType>);
}

/// # Safety
///
/// Types must be safe to transmute between each other.
pub unsafe trait TransmuteFrom<T: CompType>: Sized {}

pub trait CastType<'a, 'vir: 'a, T: CompType>: private::UnsafeCastType<'a, 'vir, T> {
    /// Only for `expr!` macro use. Use `downcast_ty`/`upcast_ty` instead.
    fn inner_cast_ty<U: CompType>(&self) -> &Self::Output<U> {
        self.cast::<U>()
    }

    /// Will panic if casting to an incorrect type.
    fn downcast_ty<U: CompType>(&self) -> &Self::Output<U>
    where
        T: TransmuteFrom<U>,
    {
        self.cast::<U>()
    }

    /// Cannot panic.
    fn upcast_ty<U: CompType + TransmuteFrom<T>>(&self) -> &Self::Output<U> {
        unsafe { self.cast_unchecked::<U>() }
    }

    /// Cannot panic.
    fn as_dyn(&self) -> &Self::Output<crate::Dyn> {
        unsafe { self.cast_unchecked::<crate::Dyn>() }
    }
}
impl<'a, 'vir: 'a, T: CompType, A: ?Sized + private::UnsafeCastType<'a, 'vir, T>>
    CastType<'a, 'vir, T> for A
{
}

macro_rules! impl_exp_type {
    ($inner:ident[$name:ident = $($const:tt)+]$( => $($up:tt)|+)?, $doc:literal) => {
        impl_exp_type!($inner[$name = $crate::TypeKind::$($const)*]$( => $($up)|+)?, $crate::TypeKind::$($const)*, $doc);
    };
    ($inner:ident$([$name:ident = $const:expr])?$( => $($up:tt)|+)?, $expected:pat$( if $cond:expr)?$( => $neg:literal)?, $doc:literal) => {
        #[doc = $doc]
        #[repr(transparent)]
        #[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
        pub struct $inner;
        #[sealed]
        impl CompType for $inner {
            fn check(ty: Type<impl CompType>) {
                if !(matches!(**ty, $expected$( if $cond)?)$( == $neg)?) {
                    $crate::typecheck_error!(
                        "Expected type `{}` but got `{ty:?}`", stringify!($expected$( if $cond)?$( == $neg)?)
                    )
                }
            }
        }

        $(pub const $name: $crate::Type<'static, $inner> = unsafe { &$crate::TypeData::new_unchecked($const) };)?
        $(
            $(
                unsafe impl TransmuteFrom<$inner> for $up {
                    // fn from(ty: $name<'vir>) -> Self {
                    //     unsafe { core::mem::transmute(ty) }
                    // }
                }
            )+
        )?
    };
}

// TODO: we could also have an `Impure` supertype of `Bool` which can contain `acc`s.
impl_exp_type!(Bool[TYPE_BOOL = Bool] => Prim | Dyn, "The Viper `Bool` type");
impl_exp_type!(Int[TYPE_INT = Int] => Prim | Dyn, "The Viper `Int` type");
impl_exp_type!(Perm[TYPE_PERM = Perm] => Prim | Dyn, "The Viper `Perm` type (reals)");
impl_exp_type!(Ref[TYPE_REF = Ref] => Prim | Dyn, "The Viper `Ref` type");
impl_exp_type!(Set => Prim | Dyn, TypeKind::Set(_), "The Viper `Set` type");

impl_exp_type!(Err[TYPE_ERR = Err] => Prim | Dyn, "Type for encoding errors");

impl_exp_type!(CSnap => Snap | Dyn, TypeKind::Domain(name, ..) if name.starts_with("s_") && name != "s_Param", "A concrete Prusti snapshot type");
impl_exp_type!(PSnap[TYPE_PSNAP = Domain("s_Param", &[])] => Snap | Dyn, "The generic snapshot domain (`s_Param`)");
impl_exp_type!(TyVal[TYPE_TYVAL = Domain("Type", &[])] => Dyn, "The type domain (`ExpType`) which gives values to types");

impl_exp_type!(Prim => Dyn, TypeKind::Bool | TypeKind::Int | TypeKind::Perm | TypeKind::Ref, "Represents any primitive Viper type");
impl_exp_type!(Snap => Dyn, TypeKind::Domain(name, ..) if name.starts_with("s_"), "A Prusti snapshot type, either concrete or generic");
impl_exp_type!(Dyn, TypeKind::Unsupported(..) => false, "Represents a dynamically typed value");

#[macro_export]
macro_rules! typecheck_error {
    ($($arg:tt)*) => {
        // if cfg!(feature = "vir_panic_on_typecheck_error") || cfg!(debug_assertions) {
        //     panic!($($arg)*);
        // } else {
            tracing::error!(
                "{}\nThe error occurred at: {}",
                format_args!($($arg)*),
                std::backtrace::Backtrace::capture()
            )
        // }
    };
}

mod private {
    use crate::{CompType, HasType};

    pub trait UnsafeCastType<'a, 'vir: 'a, T: CompType>: 'a {
        type Output<U: CompType>: 'a + ?Sized;
        fn check<U: CompType>(&self);
        unsafe fn cast_unchecked<U: CompType>(&self) -> &Self::Output<U>;

        fn cast<U: CompType>(&self) -> &Self::Output<U> {
            Self::check::<U>(self);
            unsafe { self.cast_unchecked::<U>() }
        }
    }

    impl<'a, 'vir: 'a, T: CompType, A: UnsafeCastType<'a, 'vir, T>> UnsafeCastType<'a, 'vir, T>
        for [&'a A]
    {
        type Output<U: CompType> = [&'a A::Output<U>];
        fn check<U: CompType>(&self) {
            for x in self {
                x.check::<U>();
            }
        }
        unsafe fn cast_unchecked<U: CompType>(&self) -> &Self::Output<U> {
            let other = self as *const Self as *const Self::Output<U>;
            unsafe { &*other }
        }
    }

    macro_rules! impl_unsafe_cast {
        ($($name:ident$(<$($g:ident$(: $bound:ident)?),+>)?);+) => {
            $(impl<'a, 'vir: 'a$($(, $g$(: $bound)?)*)?, T: CompType> UnsafeCastType<'a, 'vir, T> for $crate::$name<'vir$($(, $g)*)?, T> {
                type Output<U: CompType> = crate::$name<'vir$($(, $g)*)?, U>;
                fn check<U: CompType>(&self) {
                    U::check(self.ty());
                }
                /// The most general type cast. Always use `upcast_ty` or `downcast_ty` if
                /// possible. The only reason to use this if casting e.g. a generic
                /// `ExprGen<T>` type to a `ExprDyn` type.
                unsafe fn cast_unchecked<U: CompType>(&self) -> &Self::Output<U> {
                    let other = self as *const Self as *const Self::Output<U>;
                    unsafe { &*other }
                }
            })*
        };
    }
    impl_unsafe_cast!(LocalData; LocalDeclData; FieldData; AdtDestructorData<I: CompType>; ExprGenData<Curr, Next>; TypeData);
}

pub trait HasType<'vir, T: CompType> {
    fn ty(&'vir self) -> Type<'vir, T>;
    fn ty_dyn(&'vir self) -> Type<'vir, crate::Dyn> {
        self.ty().as_dyn()
    }
}

macro_rules! impl_has_type {
    ($($name:ident$(<$($g:ident$(: $bound:ident)?),+>)?$(.$t0:tt)?$(($t1:tt))?);+) => {
        $(impl<'vir$($(, $g$(: $bound)?)*)?, T: CompType> HasType<'vir, T> for $crate::$name<'vir$($(, $g)*)?, T> {
            fn ty(&'vir self) -> $crate::Type<'vir, T> {
                self$(.$t0)?$(.$t1())?
            }
        })*
    };
}

impl_has_type!(LocalData.ty; LocalDeclData.ty; FieldData.ty; AdtDestructorData<I: CompType>.ty; ExprGenData<Curr, Next>(ty); TypeData);
