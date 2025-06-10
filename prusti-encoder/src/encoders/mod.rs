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
// TODO: move `mir_impure` to this dir:
pub mod impure;

cfg_if::cfg_if! {
    if #[cfg(feature = "mono_function_encoding")] {
        pub use mono::mir_pure_function::MirMonoFunctionEnc as PureFunctionEnc;
    } else {
        pub use mir_pure_function::MirFunctionEnc as PureFunctionEnc;
    }
}

pub use domain::all_outputs as DomainEnc_all_outputs;
pub use generic::GenericEnc;
pub use impure::fn_wand::{WandEnc, WandEncOutput, WandEncTask};
pub use local_def::*;
pub use mir_builtin::{MirBuiltinEnc, MirBuiltinEncTask};
pub use mir_impure::{ImpureEncVisitor, MirImpureEnc};
pub use mir_poly_impure::MirPolyImpureEnc;
pub use mir_pure::{MirPureEnc, MirPureEncTask, PureKind};
pub use mono::{mir_impure::MirMonoImpureEnc, task_description::*};
pub use predicate::{PredicateEnc, PredicateEncOutput, PredicateEncOutputRef};
pub use pure::spec::MirSpecEnc;
pub use r#const::ConstEnc;
pub use r#type::*;
pub use snapshot::SnapshotEnc;
pub(super) use spec::with_proc_spec;
pub use spec::{is_function_trusted, is_type_trusted, SpecEnc, SpecEncOutput, SpecEncTask};
pub use viper_tuple::{ViperTupleEnc, ViperTupleEncOutput};
