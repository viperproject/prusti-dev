use task_encoder::{
    TaskEncoder,
    TaskEncoderDependencies,
};
use vir::{FunctionIdent, CallableIdent, NullaryArity};

pub struct GenericEncoder;

#[derive(Clone, Debug)]
pub enum GenericEncoderError {
    UnsupportedType,
}

#[derive(Clone, Debug)]
pub struct GenericEncoderOutputRef<'vir> {
    pub snapshot_param_name: &'vir str,
    pub predicate_param_name: &'vir str,
    pub domain_type_name: &'vir str,
}
impl<'vir> task_encoder::OutputRefAny for GenericEncoderOutputRef<'vir> {}

#[derive(Clone, Debug)]
pub struct GenericEncoderOutput<'vir> {
    pub snapshot_param: vir::Domain<'vir>,
    pub predicate_param: vir::Predicate<'vir>,
    pub domain_type: vir::Domain<'vir>,
}

use std::cell::RefCell;
thread_local! {
    static CACHE: task_encoder::CacheStaticRef<GenericEncoder> = RefCell::new(Default::default());
}

impl TaskEncoder for GenericEncoder {
    type TaskDescription<'tcx> = (); // ?

    type OutputRef<'vir> = GenericEncoderOutputRef<'vir>;
    type OutputFullLocal<'vir> = GenericEncoderOutput<'vir>;

    type EncodingError = GenericEncoderError;

    fn with_cache<'tcx: 'vir, 'vir, F, R>(f: F) -> R
        where F: FnOnce(&'vir task_encoder::CacheRef<'tcx, 'vir, GenericEncoder>) -> R,
    {
        CACHE.with(|cache| {
            // SAFETY: the 'vir and 'tcx given to this function will always be
            //   the same (or shorter) than the lifetimes of the VIR arena and
            //   the rustc type context, respectively
            let cache = unsafe { std::mem::transmute(cache) };
            f(cache)
        })
    }

    fn task_to_key<'vir>(task: &Self::TaskDescription<'vir>) -> Self::TaskKey<'vir> {
        *task
    }

    #[allow(non_snake_case)]
    fn do_encode_full<'tcx: 'vir, 'vir>(
        task_key: &Self::TaskKey<'tcx>,
        deps: &mut TaskEncoderDependencies<'vir>,
    ) -> Result<(
        Self::OutputFullLocal<'vir>,
        Self::OutputFullDependency<'vir>,
    ), (
        Self::EncodingError,
        Option<Self::OutputFullDependency<'vir>>,
    )> {
        deps.emit_output_ref::<Self>(*task_key, GenericEncoderOutputRef {
            snapshot_param_name: "s_Param",
            predicate_param_name: "p_Param",
            domain_type_name: "s_Type",
        });
        let s_Type_Bool = FunctionIdent::new("s_Type_Bool", NullaryArity::new([]));
        let s_Type_Int_isize = FunctionIdent::new("s_Type_Int_isize", NullaryArity::new([]));
        let s_Type_Int_i8 = FunctionIdent::new("s_Type_Int_i8", NullaryArity::new([]));
        let s_Type_Int_i16 = FunctionIdent::new("s_Type_Int_i16", NullaryArity::new([]));
        let s_Type_Int_i32 = FunctionIdent::new("s_Type_Int_i32", NullaryArity::new([]));
        let s_Type_Int_i64 = FunctionIdent::new("s_Type_Int_i64", NullaryArity::new([]));
        let s_Type_Int_i128 = FunctionIdent::new("s_Type_Int_i128", NullaryArity::new([]));
        let s_Type_Uint_usize = FunctionIdent::new("s_Type_Uint_usize", NullaryArity::new([]));
        let s_Type_Uint_u8 = FunctionIdent::new("s_Type_Uint_u8", NullaryArity::new([]));
        let s_Type_Uint_u16 = FunctionIdent::new("s_Type_Uint_u16", NullaryArity::new([]));
        let s_Type_Uint_u32 = FunctionIdent::new("s_Type_Uint_u32", NullaryArity::new([]));
        let s_Type_Uint_u64 = FunctionIdent::new("s_Type_Uint_u64", NullaryArity::new([]));
        let s_Type_Uint_u128 = FunctionIdent::new("s_Type_Uint_u128", NullaryArity::new([]));
        vir::with_vcx(|vcx| Ok((GenericEncoderOutput {
            snapshot_param: vir::vir_domain! { vcx; domain s_Param {} },
            predicate_param: vir::vir_predicate! { vcx; predicate p_Param(self_p: Ref/*, self_s: s_Param*/) },
            domain_type: vir::vir_domain! { vcx; domain s_Type {
                // TODO: only emit these when the types are actually used?
                //       emit instead from type encoder, to be consistent with the ADT case?
                unique function s_Type_Bool(): s_Type;
                unique function s_Type_Int_isize(): s_Type;
                unique function s_Type_Int_i8(): s_Type;
                unique function s_Type_Int_i16(): s_Type;
                unique function s_Type_Int_i32(): s_Type;
                unique function s_Type_Int_i64(): s_Type;
                unique function s_Type_Int_i128(): s_Type;
                unique function s_Type_Uint_usize(): s_Type;
                unique function s_Type_Uint_u8(): s_Type;
                unique function s_Type_Uint_u16(): s_Type;
                unique function s_Type_Uint_u32(): s_Type;
                unique function s_Type_Uint_u64(): s_Type;
                unique function s_Type_Uint_u128(): s_Type;
            } },
        }, ())))
    }
}
