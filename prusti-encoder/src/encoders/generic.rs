use task_encoder::{
    TaskEncoder,
    TaskEncoderDependencies,
};
use vir::{FunctionIdent, CallableIdent, NullaryArity, DomainIdent};

pub struct GenericEnc;

#[derive(Clone, Debug)]
pub enum GenericEncError {
    UnsupportedType,
}

#[derive(Clone, Debug)]
pub struct GenericEncOutputRef<'vir> {
    pub snapshot_param_name: &'vir str,
    pub predicate_param_name: &'vir str,
    pub domain_type_name: &'vir str,
}
impl<'vir> task_encoder::OutputRefAny for GenericEncOutputRef<'vir> {}

#[derive(Clone, Debug)]
pub struct GenericEncOutput<'vir> {
    pub snapshot_param: vir::Domain<'vir>,
    pub predicate_param: vir::Predicate<'vir>,
    pub domain_type: vir::Domain<'vir>,
}

impl TaskEncoder for GenericEnc {
    task_encoder::encoder_cache!(GenericEnc);

    type TaskDescription<'tcx> = (); // ?

    type OutputRef<'vir> = GenericEncOutputRef<'vir>;
    type OutputFullLocal<'vir> = GenericEncOutput<'vir>;

    type EncodingError = GenericEncError;

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
        deps.emit_output_ref::<Self>(*task_key, GenericEncOutputRef {
            snapshot_param_name: "s_Param",
            predicate_param_name: "p_Param",
            domain_type_name: "s_Type",
        });
        let domain_ty = &vir::TypeData::Domain("s_Type", &[]);
        let s_Type_Bool = FunctionIdent::new("s_Type_Bool", NullaryArity::new(&[]), domain_ty);
        let s_Type_Int_isize = FunctionIdent::new("s_Type_Int_isize", NullaryArity::new(&[]), domain_ty);
        let s_Type_Int_i8 = FunctionIdent::new("s_Type_Int_i8", NullaryArity::new(&[]), domain_ty);
        let s_Type_Int_i16 = FunctionIdent::new("s_Type_Int_i16", NullaryArity::new(&[]), domain_ty);
        let s_Type_Int_i32 = FunctionIdent::new("s_Type_Int_i32", NullaryArity::new(&[]), domain_ty);
        let s_Type_Int_i64 = FunctionIdent::new("s_Type_Int_i64", NullaryArity::new(&[]), domain_ty);
        let s_Type_Int_i128 = FunctionIdent::new("s_Type_Int_i128", NullaryArity::new(&[]), domain_ty);
        let s_Type_Uint_usize = FunctionIdent::new("s_Type_Uint_usize", NullaryArity::new(&[]), domain_ty);
        let s_Type_Uint_u8 = FunctionIdent::new("s_Type_Uint_u8", NullaryArity::new(&[]), domain_ty);
        let s_Type_Uint_u16 = FunctionIdent::new("s_Type_Uint_u16", NullaryArity::new(&[]), domain_ty);
        let s_Type_Uint_u32 = FunctionIdent::new("s_Type_Uint_u32", NullaryArity::new(&[]), domain_ty);
        let s_Type_Uint_u64 = FunctionIdent::new("s_Type_Uint_u64", NullaryArity::new(&[]), domain_ty);
        let s_Type_Uint_u128 = FunctionIdent::new("s_Type_Uint_u128", NullaryArity::new(&[]), domain_ty);
        vir::with_vcx(|vcx| Ok((GenericEncOutput {
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
