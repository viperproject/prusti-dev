mod generic;
mod mir_builtin;
mod mir_impure;
mod mir_pure;
mod spec;
mod mir_pure_function;
mod pure;
mod local_def;
mod r#type;
mod r#const;
mod mono;

#[cfg(feature = "mono_function_encoding")]
pub type PureFunctionEnc = mono::mir_pure_function::MirMonoFunctionEnc;

#[cfg(not(feature = "mono_function_encoding"))]
pub type PureFunctionEnc = mir_pure_function::MirFunctionEnc;

pub use pure::*;
pub use pure::spec::MirSpecEnc;
pub use local_def::*;
pub use r#type::*;
pub use generic::GenericEnc;
pub use mir_builtin::{
    MirBuiltinEnc,
    MirBuiltinEncTask,
};
pub use mir_impure::MirImpureEnc;
pub use mir_pure::{
    PureKind,
    MirPureEnc,
    MirPureEncTask,
};
pub use spec::{
    SpecEnc,
    SpecEncOutput,
    SpecEncTask,
};
pub(super) use spec::{init_def_spec, with_proc_spec};
pub use snapshot::SnapshotEnc;
pub use predicate::{
    PredicateEnc,
    PredicateEncOutputRef,
    PredicateEncOutput,
};
pub use domain::all_outputs as DomainEnc_all_outputs;
pub use viper_tuple::{
    ViperTupleEnc,
    ViperTupleEncOutput,
};
pub use r#const::ConstEnc;
