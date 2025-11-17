mod mir_builtin;
mod mir_pure;
mod mir_impure;
mod mir_shared;
mod spec;
mod pure;
mod local_def;
pub(super) mod ty;
mod r#const;
// TODO: move `mir_impure` to this dir:
pub mod impure;
/// Encoders for Rust functions (pure and impure)
pub mod mir_fn;
pub mod custom;

pub use r#const::ConstEnc;
pub use impure::fn_wand::{WandEnc, WandEncOutput, WandEncTask};
pub use local_def::*;
pub use mir_builtin::{MirBuiltinEnc, MirBuiltinEncTask};
pub use mir_fn::{FunctionCallEnc, MethodCallEnc, encode_all_in_crate};
pub use mir_impure::ImpureEncVisitor;
pub use mir_pure::{MirPureEnc, MirPureEncTask, PureKind};
pub use pure::spec::MirSpecEnc;
pub(super) use spec::with_proc_spec;
pub use spec::{SpecEnc, SpecEncTask, is_function_trusted, is_type_trusted};
pub use ty::{
    use_impure::TyUseImpureEnc,
    use_pure::TyUsePureEnc,
    viper_tuple::{ViperTupleEnc, ViperTupleEncOutput},
};

/// Some encoders work for both pure and impure encodings, though might output
/// something slightly different for the two. This allows them to be generic in
/// that regard and reuse code.
pub(crate) trait Purity:
    'static + std::fmt::Debug + Clone + Copy + PartialEq + Eq + std::hash::Hash
{
}

/// Some encoders work for both pure and impure encodings, though might output
/// something slightly different for the two. This allows them to be generic in
/// that regard and reuse code.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Pure;

impl Purity for Pure {}

/// Some encoders work for both pure and impure encodings, though might output
/// something slightly different for the two. This allows them to be generic in
/// that regard and reuse code.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Impure;

impl Purity for Impure {}
