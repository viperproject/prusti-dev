use prusti_rustc_interface::{
    middle::ty::{self, TyKind},
    target::abi,
};
use task_encoder::{EncodeFullResult, TaskEncoder, TaskEncoderDependencies};
use vir::{
    BinaryArity, CallableIdent, FunctionIdent, MethodIdent, NullaryArity, PredicateIdent, TypeData,
    UnaryArity, UnknownArity, VirCtxt,
};

use crate::encoders::GenericEnc;

use super::{
    domain::{DomainDataImmRef, DomainDataMutRef, DomainDataPrim, DomainDataStruct},
    lifted::{generic::LiftedGeneric, ty::LiftedTy},
    most_generic_ty::{get_vir_base_name_kind, MostGenericTy},
    snapshot::SnapshotEnc,
};

/// Takes a `MostGenericTy` and returns various Viper predicates and functions for
/// working with the type.
pub struct PredicateEnc;

#[derive(Clone, Debug)]
pub enum PredicateEncError {
    // UnsupportedType,
}

#[derive(Clone, Copy, Debug)]
pub struct PredicateEncDataStruct<'vir> {
    pub snap_data: DomainDataStruct<'vir>,
    /// Ref to self as argument. Returns Ref to field.
    pub ref_to_field_refs: &'vir [FunctionIdent<'vir, UnknownArity<'vir>>],
}

#[derive(Clone, Copy, Debug)]
pub struct PredicateEncDataEnum<'vir> {
    pub discr: FunctionIdent<'vir, UnaryArity<'vir>>,
    pub discr_prim: DomainDataPrim<'vir>,
    //pub discr_bounds: DiscrBounds<'vir>,
    // pub snap_to_discr_snap: FunctionIdent<'vir, UnaryArity<'vir>>,
    pub variants: &'vir [PredicateEncDataVariant<'vir>],
}
#[derive(Clone, Copy, Debug)]
pub struct PredicateEncDataVariant<'vir> {
    pub predicate: PredicateIdent<'vir, UnknownArity<'vir>>,
    pub vid: abi::VariantIdx,
    pub discr: vir::Expr<'vir>,
    pub fields: PredicateEncDataStruct<'vir>,
}

#[derive(Clone, Copy, Debug)]
pub struct PredicateEncDataImmRef<'vir> {
    pub deref_func: vir::FunctionIdent<'vir, BinaryArity<'vir>>,
    pub perm: Option<vir::Expr<'vir>>,
    pub snap_data: DomainDataImmRef<'vir>,
}

#[derive(Clone, Copy, Debug)]
pub struct PredicateEncDataMutRef<'vir> {
    pub deref_func: vir::FunctionIdent<'vir, UnaryArity<'vir>>,
    pub perm: Option<vir::Expr<'vir>>,
    pub snap_data: DomainDataMutRef<'vir>,
}

#[derive(Clone, Copy, Debug)]
pub enum PredicateEncData<'vir> {
    Never,
    Primitive(DomainDataPrim<'vir>),
    // structs, tuples
    Trusted,
    StructLike(PredicateEncDataStruct<'vir>),
    EnumLike(Option<PredicateEncDataEnum<'vir>>),
    ImmRef(PredicateEncDataImmRef<'vir>),
    MutRef(PredicateEncDataMutRef<'vir>),
    Param,
}

// TODO: should output refs actually be references to structs...?
#[derive(Clone, Debug)]
pub struct PredicateEncOutputRef<'vir> {
    /// Constructs the Viper predicate application.
    pub ref_to_pred: PredicateIdent<'vir, UnknownArity<'vir>>,
    /// Construct snapshot from Viper ref.
    pub ref_to_snap: FunctionIdent<'vir, UnknownArity<'vir>>,
    /// Ref as first argument, followed by type parameters, followed by
    /// snapshot. Ensures predicate access to ref with snapshot value. This
    /// probably shouldn't be accessed directly, instead see
    /// `RustTyPredicatesEncOutputRef::apply_method_assign`.
    pub(super) method_assign: MethodIdent<'vir, UnknownArity<'vir>>,
    /// Construct snapshot from an unreachable.
    pub unreachable_to_snap: FunctionIdent<'vir, NullaryArity<'vir>>,
    /// Always `TypeData::Domain`.
    pub snapshot: vir::Type<'vir>,
    //pub method_refold: &'vir str,
    pub specifics: PredicateEncData<'vir>,
    #[allow(dead_code)]
    pub generics: &'vir [vir::LocalDecl<'vir>],

    //pub ref_to_lifetime_pred: HashMap<ty::Region<'vir>, ()>,
    pub ref_to_indirect_pred: Option<vir::ExprGen<'vir, vir::Expr<'vir>, vir::ExprKind<'vir>>>,
}
impl<'vir> task_encoder::OutputRefAny for PredicateEncOutputRef<'vir> {}

impl<'vir> PredicateEncOutputRef<'vir> {
    /// Constructs arguments for [`PredicateEncOutputRef::ref_to_pred`] and
    /// [`PredicateEncOutputRef::ref_to_snap`]. Takes as input a Ref representing
    /// the self, and the encoded Rust type (see [`LiftedTy`]). The arguments to the
    /// function are the type arguments of the lifted type.
    pub fn ref_to_args<'tcx>(
        &self,
        vcx: &'vir vir::VirCtxt<'tcx>,
        instantiated_ty: LiftedTy<'vir, LiftedGeneric<'vir>>,
        self_ref: vir::Expr<'vir>,
    ) -> &'vir [vir::Expr<'vir>] {
        assert!(self_ref.ty() == &TypeData::Ref);
        let mut args = vec![self_ref];
        args.extend(instantiated_ty.arg_exprs(vcx));
        vcx.alloc_slice(&args)
    }

    #[track_caller]
    pub fn expect_prim(&self) -> DomainDataPrim<'vir> {
        match self.specifics {
            PredicateEncData::Primitive(prim) => prim,
            _ => panic!("expected primitive type"),
        }
    }
    #[track_caller]
    pub fn expect_immref(&self) -> PredicateEncDataImmRef<'vir> {
        match self.specifics {
            PredicateEncData::ImmRef(r) => r,
            s => panic!("expected immref type ({s:?})"),
        }
    }
    #[track_caller]
    pub fn expect_mutref(&self) -> PredicateEncDataMutRef<'vir> {
        match self.specifics {
            PredicateEncData::MutRef(r) => r,
            s => panic!("expected mutref type ({s:?})"),
        }
    }
    pub fn get_structlike(&self) -> Option<&PredicateEncDataStruct<'vir>> {
        match &self.specifics {
            PredicateEncData::StructLike(data) => Some(data),
            _ => None,
        }
    }
    #[track_caller]
    pub fn expect_structlike(&self) -> &PredicateEncDataStruct<'vir> {
        self.get_structlike().expect("expected structlike type")
    }
    pub fn get_enumlike(&self) -> Option<&Option<PredicateEncDataEnum<'vir>>> {
        match &self.specifics {
            PredicateEncData::EnumLike(e) => Some(e),
            _ => None,
        }
    }
    #[track_caller]
    pub fn expect_enumlike(&self) -> Option<&PredicateEncDataEnum<'vir>> {
        self.get_enumlike()
            .expect("expected enumlike type")
            .as_ref()
    }
    pub fn get_variant_any(&self, vid: abi::VariantIdx) -> &PredicateEncDataStruct<'vir> {
        match &self.specifics {
            PredicateEncData::StructLike(s) => {
                assert_eq!(vid, abi::FIRST_VARIANT);
                s
            }
            PredicateEncData::EnumLike(e) => &e.as_ref().unwrap().variants[vid.as_usize()].fields,
            _ => panic!("expected structlike or enumlike type"),
        }
    }

    #[track_caller]
    pub fn expect_variant(&self, vid: abi::VariantIdx) -> &PredicateEncDataVariant<'vir> {
        match &self.specifics {
            PredicateEncData::EnumLike(e) => &e.as_ref().unwrap().variants[vid.as_usize()],
            _ => panic!("expected enum type"),
        }
    }
    #[track_caller]
    pub fn expect_pred_variant_opt(
        &self,
        vid: Option<abi::VariantIdx>,
    ) -> PredicateIdent<'vir, UnknownArity<'vir>> {
        vid.map(|vid| self.expect_variant(vid).predicate)
            .unwrap_or(self.ref_to_pred)
    }
    #[track_caller]
    pub fn expect_variant_opt(
        &self,
        vid: Option<abi::VariantIdx>,
    ) -> &PredicateEncDataStruct<'vir> {
        match vid {
            None => self.expect_structlike(),
            Some(vid) => {
                &self.expect_enumlike().expect("empty enum").variants[vid.as_usize()].fields
            }
        }
    }
}

pub(crate) struct PredicateBuilder<'vir> {
    pub(crate) vcx: &'vir vir::VirCtxt<'vir>,
    name: Option<&'vir str>,
    pub(crate) fields: Vec<vir::Field<'vir>>,
    pub(crate) predicates: Vec<vir::Predicate<'vir>>,
    pub(crate) functions: Vec<vir::Function<'vir>>,
    pub(crate) methods: Vec<vir::Method<'vir>>,

    // TODO: function idents!
    pub(crate) unreachable_to_snap: Option<(
        vir::FunctionIdent<'vir, NullaryArity<'vir>>,
        vir::Function<'vir>,
    )>,
    pub(crate) function_snap: Option<vir::Function<'vir>>,
}

impl<'vir> PredicateBuilder<'vir> {
    pub(crate) fn new(vcx: &'vir vir::VirCtxt<'vir>) -> Self {
        PredicateBuilder {
            vcx,
            name: None,
            fields: Vec::new(),
            functions: Vec::new(),
            methods: Vec::new(),
            predicates: Vec::new(),
            unreachable_to_snap: None,
            function_snap: None,
        }
    }

    pub(crate) fn set_name(&mut self, name: &str) {
        let name = vir::vir_format!(self.vcx, "p_{name}");
        self.name = Some(name);
    }

    fn ident_str(&self, name: &str) -> &'vir str {
        let prefix = self.name.expect("name should be set");
        if name.is_empty() {
            prefix
        } else {
            vir::vir_format!(self.vcx, "{prefix}_{name}")
        }
    }

    pub(crate) fn field(&mut self, name: &str, typ: vir::Type<'vir>) -> vir::Field<'vir> {
        let name = self.ident_str(name);
        let field = self.vcx.mk_field(name, typ);
        self.fields.push(field);
        field
    }

    pub(crate) fn predicate_ident(
        &mut self,
        name: &str,
        args: &[vir::LocalDecl<'vir>],
    ) -> vir::PredicateIdent<'vir, vir::UnknownArity<'vir>> {
        let name = self.ident_str(name);
        let ident = vir::PredicateIdent::new(
            vir::ViperIdent::new(name),
            vir::UnknownArity::new(
                self.vcx
                    .alloc_slice(&args.iter().map(|arg| arg.ty).collect::<Vec<_>>()),
            ),
        );
        ident
    }

    pub(crate) fn predicate(
        &mut self,
        name: &str,
        args: &[vir::LocalDecl<'vir>],
        expr: Option<vir::Expr<'vir>>,
    ) -> vir::PredicateIdent<'vir, vir::UnknownArity<'vir>> {
        let ident = self.predicate_ident(name, args);
        self.predicates.push(
            self.vcx
                .mk_predicate(ident, self.vcx.alloc_slice(args), expr),
        );
        ident
    }

    pub(crate) fn function_ident(
        &mut self,
        name: &str,
        args: &[vir::LocalDecl<'vir>],
        ret: vir::Type<'vir>,
    ) -> vir::FunctionIdent<'vir, vir::UnknownArity<'vir>> {
        let name = self.ident_str(name);
        let ident = vir::FunctionIdent::new(
            vir::ViperIdent::new(name),
            vir::UnknownArity::new(
                self.vcx
                    .alloc_slice(&args.iter().map(|arg| arg.ty).collect::<Vec<_>>()),
            ),
            ret,
        );
        ident
    }

    pub(crate) fn mk_function(
        &self,
        name: &str,
        args: &[vir::LocalDecl<'vir>],
        ret: vir::Type<'vir>,
        pres: &[vir::Expr<'vir>],
        posts: &[vir::Expr<'vir>],
        expr: Option<vir::Expr<'vir>>,
    ) -> (
        vir::FunctionIdent<'vir, vir::UnknownArity<'vir>>,
        vir::Function<'vir>,
    ) {
        let name = self.ident_str(name);
        let ident = vir::FunctionIdent::new(
            vir::ViperIdent::new(name),
            vir::UnknownArity::new(
                self.vcx
                    .alloc_slice(&args.iter().map(|arg| arg.ty).collect::<Vec<_>>()),
            ),
            ret,
        );
        (
            ident,
            self.vcx.mk_function(
                name,
                self.vcx.alloc_slice(args),
                ret,
                self.vcx.alloc_slice(pres),
                self.vcx.alloc_slice(posts),
                expr,
            ),
        )
    }

    pub(crate) fn function(
        &mut self,
        name: &str,
        args: &[vir::LocalDecl<'vir>],
        ret: vir::Type<'vir>,
        pres: &[vir::Expr<'vir>],
        posts: &[vir::Expr<'vir>],
        expr: Option<vir::Expr<'vir>>,
    ) -> vir::FunctionIdent<'vir, UnknownArity<'vir>> {
        let (ident, function) = self.mk_function(name, args, ret, pres, posts, expr);
        self.functions.push(function);
        ident
    }

    pub(crate) fn method(
        &mut self,
        name: &str,
        args: &[vir::LocalDecl<'vir>],
        rets: &[vir::LocalDecl<'vir>],
        pres: &[vir::Expr<'vir>],
        posts: &[vir::Expr<'vir>],
    ) -> vir::MethodIdent<'vir, UnknownArity<'vir>> {
        let name = self.ident_str(name);
        let ident = MethodIdent::new(
            vir::ViperIdent::new(name),
            UnknownArity::new(
                self.vcx
                    .alloc_slice(&args.iter().map(|arg| arg.ty).collect::<Vec<_>>()),
            ),
            //ret,
        );
        self.methods.push(self.vcx.mk_method(
            ident,
            self.vcx.alloc_slice(args),
            self.vcx.alloc_slice(rets),
            self.vcx.alloc_slice(pres),
            self.vcx.alloc_slice(posts),
            None,
        ));
        ident
    }

    pub(crate) fn build(self) -> PredicateEncOutput<'vir> {
        PredicateEncOutput {
            fields: self.fields,
            predicates: self.predicates,
            unreachable_to_snap: self.unreachable_to_snap.unwrap().1,
            function_snap: self.function_snap.unwrap(),
            ref_to_field_refs: self.functions,
            method_assign: self.methods[0],
        }
    }
}

#[derive(Clone, Debug)]
pub struct PredicateEncOutput<'vir> {
    pub fields: Vec<vir::Field<'vir>>,
    pub predicates: Vec<vir::Predicate<'vir>>,
    // TODO: these should be generated on demand, put into tiny encoders ?
    pub unreachable_to_snap: vir::Function<'vir>,
    pub function_snap: vir::Function<'vir>,
    pub ref_to_field_refs: Vec<vir::Function<'vir>>,
    pub method_assign: vir::Method<'vir>,
}

impl TaskEncoder for PredicateEnc {
    task_encoder::encoder_cache!(PredicateEnc);

    type TaskDescription<'vir> = MostGenericTy<'vir>;

    type OutputRef<'vir> = PredicateEncOutputRef<'vir>;
    type OutputFullLocal<'vir> = PredicateEncOutput<'vir>;
    //type OutputFullDependency<'vir> = PredicateEncOutputDep<'vir>;

    type EncodingError = PredicateEncError;

    fn task_to_key<'vir>(task: &Self::TaskDescription<'vir>) -> Self::TaskKey<'vir> {
        *task
    }

    fn do_encode_full<'vir>(
        task_key: &Self::TaskKey<'vir>,
        deps: &mut TaskEncoderDependencies<'vir, Self>,
    ) -> EncodeFullResult<'vir, Self> {
        let snap = deps.require_local::<SnapshotEnc>(*task_key)?;
        let generic_output_ref = deps.require_ref::<GenericEnc>(())?;

        if let TyKind::Param(..) = task_key.kind() {
            let method_assign = vir::with_vcx(|vcx| {
                MethodIdent::new(
                    vir::ViperIdent::new("assign_p_Param"),
                    UnknownArity::new(vcx.alloc_slice(&[
                        &TypeData::Ref,
                        generic_output_ref.type_snapshot,
                        generic_output_ref.param_snapshot,
                    ])),
                )
            });
            deps.emit_output_ref(
                *task_key,
                PredicateEncOutputRef {
                    ref_to_pred: generic_output_ref.ref_to_pred.as_unknown_arity(),
                    ref_to_snap: generic_output_ref.ref_to_snap.as_unknown_arity(),
                    unreachable_to_snap: generic_output_ref.unreachable_to_snap,
                    method_assign,
                    snapshot: generic_output_ref.param_snapshot,
                    specifics: PredicateEncData::Param,
                    generics: &[],
                    ref_to_indirect_pred: None,
                },
            )?;
            let dep = deps.require_local::<GenericEnc>(())?;
            return vir::with_vcx(|vcx| {
                let method_assign = mk_method_assign(
                    vcx,
                    method_assign,
                    vec![vcx.mk_local_decl("t", generic_output_ref.type_snapshot)],
                    generic_output_ref.param_snapshot,
                    generic_output_ref.ref_to_pred.as_unknown_arity(),
                    generic_output_ref.ref_to_snap.as_unknown_arity(),
                );
                Ok((
                    PredicateEncOutput {
                        fields: vec![],
                        predicates: vec![dep.ref_to_pred],
                        unreachable_to_snap: dep.unreachable_to_snap,
                        function_snap: dep.ref_to_snap,
                        ref_to_field_refs: vec![],
                        method_assign,
                    },
                    (),
                ))
            });
        }

        if let Some(res) = vir::with_vcx(|vcx| {
            let mut builder = PredicateBuilder::new(vcx);

            let base_name = get_vir_base_name_kind(task_key.kind(), vcx);
            builder.set_name(&base_name);

            let snap_type = snap.snapshot;
            let ref_self = vcx.mk_local("self", &vir::TypeData::Ref);
            let ref_self_decl = vcx.mk_local_decl_local(ref_self);

            let generic_decls = snap.generics.iter().map(|g| g.decl()).collect::<Vec<_>>();
            let generic_exprs = snap
                .generics
                .iter()
                .map(|g| g.expr(builder.vcx))
                .collect::<Vec<_>>();

            let self_pred_ident = builder.predicate_ident(
                "",
                &[ref_self_decl]
                    .into_iter()
                    .chain(generic_decls.iter().cloned())
                    .collect::<Vec<_>>(),
            );
            let snap_func_ident = builder.function_ident(
                "snap",
                &[ref_self_decl]
                    .into_iter()
                    .chain(generic_decls.iter().cloned())
                    .collect::<Vec<_>>(),
                snap_type,
            );

            // unreachable (requires false) to snap (TODO: move to domain enc)
            use vir::ToKnownArity;
            let (unr_ident, unr_func) = builder.mk_function(
                "unreachable",
                &[],
                snap_type,
                &[vcx.mk_bool::<false>()],
                &[vcx.mk_bool::<false>()], // TODO: is this necessary?
                None,
            );
            builder.unreachable_to_snap = Some((unr_ident.to_known(), unr_func));

            // assign method
            let value = vcx.mk_local("value", snap_type);
            let method_assign = builder.method(
                "assign",
                &[ref_self_decl]
                    .into_iter()
                    .chain(generic_decls.iter().cloned())
                    .chain([vcx.mk_local_decl_local(value)])
                    .collect::<Vec<_>>(),
                &[],
                &[],
                &[
                    vir::expr! { [self_pred_ident](ref_self, ..[generic_exprs]) },
                    vir::expr! { ([snap_func_ident](ref_self, ..[generic_exprs])) == (value) },
                ],
            );

            if crate::encoders::spec::is_type_trusted(task_key.ty()) {
                let args = &[ref_self_decl]
                    .into_iter()
                    .chain(generic_decls.iter().cloned())
                    .collect::<Vec<_>>();
                builder.predicate("", &args, None);
                builder.function_snap = Some(
                    builder
                        .mk_function("snap", &args, snap_type, &[], &[], None)
                        .1,
                );
                deps.emit_output_ref(
                    *task_key,
                    PredicateEncOutputRef {
                        ref_to_pred: self_pred_ident,
                        ref_to_snap: snap_func_ident,
                        unreachable_to_snap: builder.unreachable_to_snap.unwrap().0,
                        method_assign,
                        snapshot: snap_type,
                        specifics: PredicateEncData::Trusted,
                        generics: vcx.alloc_slice(&generic_decls),
                        ref_to_indirect_pred: None,
                    },
                )?;
                return Ok(Some(builder.build()));
            }

            let (specifics, ref_to_indirect_pred) = match task_key.kind() {
                TyKind::Bool
                | TyKind::Char
                | TyKind::Int(_)
                | TyKind::Uint(_)
                | TyKind::Float(_) => {
                    super::kinds::primitive::predicate(*task_key, snap.clone(), deps, &mut builder)?
                }
                TyKind::Adt(..) => super::kinds::adt::predicate(
                    *task_key,
                    snap.clone(),
                    deps,
                    &generic_decls,
                    &generic_exprs,
                    &mut builder,
                )?,
                TyKind::Ref(_, _, ty::Mutability::Not) => super::kinds::immref::predicate(
                    *task_key,
                    snap.clone(),
                    deps,
                    &generic_decls,
                    &generic_exprs,
                    &mut builder,
                )?,
                TyKind::Ref(_, _, ty::Mutability::Mut) => super::kinds::mutref::predicate(
                    *task_key,
                    snap.clone(),
                    deps,
                    /*&generic_decls, &generic_exprs, */ &mut builder,
                )?,
                TyKind::Never => (
                    super::kinds::never::predicate(
                        *task_key,
                        snap.clone(),
                        deps,
                        /*&generic_decls, &generic_exprs, */ &mut builder,
                    )?,
                    None,
                ),
                TyKind::Closure(..) => (
                    super::kinds::closure::predicate(
                        *task_key,
                        snap.clone(),
                        deps,
                        &generic_decls,
                        &generic_exprs,
                        &mut builder,
                    )?,
                    None,
                ),
                TyKind::Tuple(..) => (
                    super::kinds::tuple::predicate(
                        *task_key,
                        snap.clone(),
                        deps,
                        &generic_decls,
                        &generic_exprs,
                        &mut builder,
                    )?,
                    None,
                ),
                TyKind::Str => (
                    super::kinds::str::predicate(*task_key, snap.clone(), deps, &mut builder)?,
                    None,
                ),
                TyKind::Param(_) => unreachable!(),
                _ => return Ok(None),
            };

            deps.emit_output_ref(
                *task_key,
                PredicateEncOutputRef {
                    ref_to_pred: self_pred_ident,
                    ref_to_snap: snap_func_ident,
                    unreachable_to_snap: builder.unreachable_to_snap.unwrap().0,
                    method_assign,
                    snapshot: snap_type,
                    specifics,
                    generics: vcx.alloc_slice(&generic_decls),
                    ref_to_indirect_pred,
                },
            )?;

            Ok(Some(builder.build()))
        })? {
            return Ok((res, ()));
        }

        match task_key.kind() {
            TyKind::Bool | TyKind::Char | TyKind::Int(_) | TyKind::Uint(_) | TyKind::Float(_) => {
                unreachable!()
            }
            TyKind::Adt(..) => unreachable!(),
            TyKind::Ref(..) => unreachable!(),
            TyKind::Param(_) => unreachable!(),
            TyKind::Closure(..) => unreachable!(),
            TyKind::Never => unreachable!(),
            TyKind::Tuple(..) => unreachable!(),
            TyKind::Str => unreachable!(),
            unsupported_type => todo!("type not supported: {unsupported_type:?}"),
        }
    }
}

fn mk_method_assign<'vir>(
    vcx: &'vir VirCtxt<'_>,
    ident: MethodIdent<'vir, UnknownArity<'vir>>,
    generics: Vec<vir::LocalDecl<'vir>>,
    snapshot: vir::Type<'vir>,
    ref_to_pred: PredicateIdent<'vir, UnknownArity<'vir>>,
    ref_to_snap: FunctionIdent<'vir, UnknownArity<'vir>>,
) -> vir::Method<'vir> {
    let self_local = vcx.mk_local_decl("self", &TypeData::Ref);
    let self_new_local = vcx.mk_local_decl("self_new", snapshot);

    let ref_to_args = std::iter::once(&self_local)
        .chain(generics.iter())
        .map(|decl| vcx.mk_local_ex(decl.name, decl.ty))
        .collect::<Vec<_>>();

    let self_pred_app = vcx.mk_predicate_app_expr(ref_to_pred.apply(vcx, &ref_to_args, None));

    let mut assign_args = vec![self_local];
    assign_args.extend(generics);
    assign_args.push(self_new_local);
    let assign_args = vcx.alloc_slice(&assign_args);

    let posts = vcx.alloc_slice(&[
        self_pred_app,
        vcx.mk_eq_expr(
            ref_to_snap.apply(vcx, &ref_to_args),
            vcx.mk_local_ex(self_new_local.name, snapshot),
        ),
    ]);
    vcx.mk_method(ident, assign_args, &[], &[], posts, None)
}
