mod generic;
mod mir_builtin;
mod mir_pure;
mod mir_poly_impure;
mod mir_impure;
mod spec;
mod mir_pure_function;
mod pure;
mod local_def;
mod r#type;
mod r#const;
mod mono;

cfg_if::cfg_if! {
    if #[cfg(feature = "mono_function_encoding")] {
        pub use mono::mir_pure_function::MirMonoFunctionEnc as PureFunctionEnc;
    } else {
        pub use mir_pure_function::MirFunctionEnc as PureFunctionEnc;
    }
}


pub use mono::task_description::*;
pub use pure::*;
pub use pure::spec::MirSpecEnc;
pub use local_def::*;
pub use r#type::*;
pub use generic::GenericEnc;
pub use mir_builtin::{
    MirBuiltinEnc,
    MirBuiltinEncTask,
};
pub use mir_poly_impure::MirPolyImpureEnc;
pub use mono::mir_impure::MirMonoImpureEnc;
pub use mir_impure::{ImpureEncVisitor, MirImpureEnc};
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
