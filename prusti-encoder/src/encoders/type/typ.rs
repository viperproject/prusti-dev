use prusti_rustc_interface::{
    middle::ty::{self, TyKind, util::IntTypeExt},
    abi,
};
use task_encoder::{
    TaskEncoder,
    TaskEncoderDependencies,
};
use vir::{BinaryArity, UnaryArity, NullaryArity, UnknownArity, FunctionIdent, MethodIdent, PredicateIdent, CallableIdent};

pub struct TypeEncoder;

#[derive(Clone, Debug)]
pub enum TypeEncoderError {
    UnsupportedType,
}

#[derive(Clone, Copy, Debug)]
pub struct FieldAccessFunctions<'vir> {
    /// Snapshot of self as argument. Returns snapshot of field.
    pub read: FunctionIdent<'vir, UnaryArity<'vir>>,
    /// Snapshot of self as first argument and of field as second. Returns
    /// updated snapshot of self.
    pub write: FunctionIdent<'vir, BinaryArity<'vir>>,
    /// Ref to self as argument. Returns Ref to field.
    pub projection_p: FunctionIdent<'vir, UnaryArity<'vir>>,
}

#[derive(Clone, Debug)]
pub struct TypeEncoderOutputRefSubPrim<'vir> {
    pub prim_type: vir::Type<'vir>,
    /// Snapshot of self as argument. Returns Viper primitive value.
    pub snap_to_prim: FunctionIdent<'vir, UnaryArity<'vir>>,
    /// Viper primitive value as argument. Returns snapshot.
    pub prim_to_snap: FunctionIdent<'vir, UnaryArity<'vir>>,
}

#[derive(Clone, Debug)]
pub struct TypeEncoderOutputRefSubStruct<'vir> {
    /// Construct snapshot from snapshots of fields or for primitive types
    /// from the single Viper primitive value. `None` for generic parameters.
    pub field_snaps_to_snap: FunctionIdent<'vir, UnknownArity<'vir>>,
    /// Functions to access the fields.
    pub field_access: &'vir [FieldAccessFunctions<'vir>],
}

#[derive(Clone, Debug)]
pub struct TypeEncoderOutputRefSubEnum<'vir> {
    pub field_discriminant: &'vir str,
    pub snap_to_disc_snap: FunctionIdent<'vir, UnaryArity<'vir>>,
    pub variants: &'vir [(TypeEncoderOutputRefSubStruct<'vir>, PredicateIdent<'vir, UnaryArity<'vir>>)],
}

#[derive(Clone, Debug)]
pub enum TypeEncoderOutputRefSub<'vir> {
    Primitive(TypeEncoderOutputRefSubPrim<'vir>),
    // structs, tuples
    StructLike(TypeEncoderOutputRefSubStruct<'vir>),
    EnumLike(TypeEncoderOutputRefSubEnum<'vir>),
    Param,
}

// TODO: should output refs actually be references to structs...?
#[derive(Clone, Debug)]
pub struct TypeEncoderOutputRef<'vir> {
    /// Constructs the Viper predicate application.
    pub ref_to_pred: PredicateIdent<'vir, UnaryArity<'vir>>,
    /// Construct snapshot from Viper predicate.
    pub ref_to_snap: FunctionIdent<'vir, UnaryArity<'vir>>,
    /// Construct snapshot from an unreachable.
    pub unreachable_to_snap: FunctionIdent<'vir, NullaryArity>,
    /// Ref as first argument, snapshot as second. Ensures predicate
    /// access to ref with snapshot value.
    pub method_assign: MethodIdent<'vir, BinaryArity<'vir>>,
    /// Always `TypeData::Domain`.
    pub snapshot: vir::Type<'vir>,
    //pub method_refold: &'vir str,
    pub specifics: TypeEncoderOutputRefSub<'vir>,
}
impl<'vir> task_encoder::OutputRefAny for TypeEncoderOutputRef<'vir> {}

impl<'vir> TypeEncoderOutputRef<'vir> {
    pub fn expect_structlike(&self) -> &TypeEncoderOutputRefSubStruct<'vir> {
        match &self.specifics {
            TypeEncoderOutputRefSub::StructLike(data) => data,
            _ => panic!("expected structlike type"),
        }
    }
    pub fn expect_prim(&self) -> &TypeEncoderOutputRefSubPrim<'vir> {
        match &self.specifics {
            TypeEncoderOutputRefSub::Primitive(prim) => prim,
            _ => panic!("expected primitive type"),
        }
    }
    pub fn expect_enumlike(&self) -> &TypeEncoderOutputRefSubEnum<'vir> {
        match &self.specifics {
            TypeEncoderOutputRefSub::EnumLike(enu) => enu,
            _ => panic!("expected enumlike type"),
        }
    }
    pub fn expect_variant(&self, vid: abi::VariantIdx) -> &TypeEncoderOutputRefSubStruct<'vir> {
        match &self.specifics {
            TypeEncoderOutputRefSub::StructLike(s) => {
                assert_eq!(vid, abi::FIRST_VARIANT);
                s
            }
            TypeEncoderOutputRefSub::EnumLike(e) => &e.variants[vid.as_usize()].0,
            _ => panic!("expected struct or enum type"),
        }
    }
    pub fn expect_variant_opt(&self, vid: Option<abi::VariantIdx>) -> &TypeEncoderOutputRefSubStruct<'vir> {
        match &self.specifics {
            TypeEncoderOutputRefSub::StructLike(s) => {
                assert_eq!(vid, None);
                s
            }
            TypeEncoderOutputRefSub::EnumLike(e) => &e.variants[vid.unwrap().as_usize()].0,
            _ => panic!("expected struct or enum type"),
        }
    }

    pub fn expr_from_u128(&self, val: u128) -> vir::Expr<'vir> {
        match self.expect_prim().prim_type {
            vir::TypeData::Bool => vir::with_vcx(|vcx| {
                self.expect_prim().prim_to_snap.apply(vcx, [vcx.mk_const_expr(vir::ConstData::Bool(val != 0))])
            }),
            vir::TypeData::Int { .. } => vir::with_vcx(|vcx| {
                self.expect_prim().prim_to_snap.apply(vcx, [
                    vcx.mk_const_expr(vir::ConstData::Int(val))
                ])
            }),
            k => {
                tracing::error!(
                    "unsupported type in expr_from_u128: {self:?} | {k:?} | ({:?})",
                    self.snapshot
                );
                vir::with_vcx(|vcx| {
                    vcx.alloc(vir::ExprData::Const(vcx.alloc(vir::ConstData::Int(val))))
                })
            }
        }
    }
}

#[derive(Clone, Debug)]
pub struct TypeEncoderOutput<'vir> {
    pub fields: &'vir [vir::Field<'vir>],
    pub snapshot: vir::Domain<'vir>,
    pub predicate: vir::Predicate<'vir>,
    pub other_predicates: &'vir [vir::Predicate<'vir>],
    // TODO: these should be generated on demand, put into tiny encoders ?
    pub unreachable_to_snap: vir::Function<'vir>,
    pub function_snap: vir::Function<'vir>,
    pub field_projection_p: &'vir [vir::Function<'vir>],
    //pub method_refold: vir::Method<'vir>,
    pub method_assign: vir::Method<'vir>,
}

use std::cell::RefCell;
thread_local! {
    static CACHE: task_encoder::CacheStaticRef<TypeEncoder> = RefCell::new(Default::default());
}

impl TaskEncoder for TypeEncoder {
    type TaskDescription<'vir> = ty::Ty<'vir>;

    type OutputRef<'vir> = TypeEncoderOutputRef<'vir>;
    type OutputFullLocal<'vir> = TypeEncoderOutput<'vir>;
    //type OutputFullDependency<'vir> = TypeEncoderOutputDep<'vir>;

    type EncodingError = TypeEncoderError;

    fn with_cache<'tcx: 'vir, 'vir, F, R>(f: F) -> R
        where F: FnOnce(&'vir task_encoder::CacheRef<'tcx, 'vir, TypeEncoder>) -> R,
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
        // Here we need to normalise the task description.
        // In particular, any concrete type parameter instantiation is replaced
        // with the identity substitutions for the item.
        // For example:
        //     Assuming `struct Foo<T, U> { .. }`,
        //     `Foo<i32, bool>` is normalised to `Foo<T, U>`
        match task.kind() {
            /*TyKind::Param(_) => vir::with_vcx(|vcx| vcx.tcx.mk_ty_param(
                0,
                vcx.tcx.mk_symbol("T"),
            )),*/
            TyKind::Adt(adt_def, _) if adt_def.is_struct() => vir::with_vcx(|vcx| {
                let substs = ty::List::identity_for_item(vcx.tcx, adt_def.did());
                vcx.tcx.mk_ty_from_kind(ty::TyKind::Adt(*adt_def, substs))
            }),
            _ => *task,
        }
    }

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
        vir::with_vcx(|vcx| match task_key.kind() {
            TyKind::Bool => {
                let ty_s = vcx.alloc(vir::TypeData::Domain("s_Bool"));
                let ref_to_pred = Self::mk_predicate_ident("p_Bool");
                let ref_to_snap = Self::mk_function_snap_identifier(vcx, "p_Bool", ty_s);
                let unreachable_to_snap = Self::mk_function_unreachable_identifier(vcx, "s_Bool");
                let method_assign = Self::mk_function_assign(vcx, "p_Bool", ty_s);
                let (snap_to_prim, prim_to_snap) = Self::mk_primitive(vcx, "s_Bool", ty_s, &vir::TypeData::Bool);
                let specifics = TypeEncoderOutputRefSub::Primitive(TypeEncoderOutputRefSubPrim {
                    prim_type: &vir::TypeData::Bool,
                    snap_to_prim,
                    prim_to_snap,
                });
                deps.emit_output_ref::<Self>(*task_key, TypeEncoderOutputRef {
                    ref_to_pred,
                    snapshot: ty_s,
                    unreachable_to_snap,
                    ref_to_snap,
                    //method_refold: "refold_p_Bool",
                    specifics,
                    method_assign,
                });
                Ok((TypeEncoderOutput {
                    fields: vcx.alloc_slice(&[vcx.alloc(vir::FieldData {
                        name: "f_Bool",
                        ty: ty_s,
                    })]),
                    snapshot: vir::vir_domain! { vcx; domain s_Bool {
                        function prim_to_snap(Bool): s_Bool;
                        function snap_to_prim(s_Bool): Bool;
                        axiom_inverse(snap_to_prim, prim_to_snap, Bool);
                    } },
                    predicate: Self::mk_simple_predicate(vcx, "p_Bool", "f_Bool"),
                    other_predicates: &[],
                    unreachable_to_snap: Self::mk_unreachable(vcx, unreachable_to_snap, ty_s),
                    function_snap: Self::mk_snap(vcx, ref_to_pred, ref_to_snap, Some("f_Bool"), ty_s),
                    //method_refold: mk_refold(vcx, "p_Bool", ty_s),
                    field_projection_p: &[],
                    method_assign: Self::mk_assign(vcx, ref_to_pred, method_assign, ref_to_snap, ty_s),
                }, ()))
            }
            TyKind::Int(_) |
            TyKind::Uint(_) => {
                let signed = task_key.is_signed();
                let (sign, name_str) = match task_key.kind() {
                    TyKind::Int(kind) => ("Int", kind.name_str()),
                    TyKind::Uint(kind) => ("Uint", kind.name_str()),
                    _ => unreachable!(),
                };
                let bit_width = Self::get_bit_width(vcx.tcx, *task_key);
                let prim_type = vcx.alloc(vir::TypeData::Int { bit_width: bit_width as u8, signed });
                let name_s = vir::vir_format!(vcx, "s_{sign}_{name_str}");
                let name_p = vir::vir_format!(vcx, "p_{sign}_{name_str}");
                let ref_to_pred = Self::mk_predicate_ident(name_p);
                let ty_s = vcx.alloc(vir::TypeData::Domain(name_s));
                let (snap_to_prim, prim_to_snap) = Self::mk_primitive(vcx, name_s, ty_s, prim_type);
                let name_field = vir::vir_format!(vcx, "f_{name_s}");
                let ref_to_snap = Self::mk_function_snap_identifier(vcx, name_p, ty_s);
                let unreachable_to_snap = Self::mk_function_unreachable_identifier(vcx, name_s);
                let method_assign = Self::mk_function_assign(vcx, name_p, ty_s);
                let specifics = TypeEncoderOutputRefSub::Primitive(TypeEncoderOutputRefSubPrim {
                    prim_type,
                    snap_to_prim,
                    prim_to_snap,
                });
                deps.emit_output_ref::<Self>(*task_key, TypeEncoderOutputRef {
                    ref_to_pred,
                    snapshot: ty_s,
                    unreachable_to_snap,
                    ref_to_snap,
                    //method_refold: vir::vir_format!(vcx, "refold_{name_p}"),
                    specifics,
                    method_assign,
                });
                Ok((TypeEncoderOutput {
                    fields: vcx.alloc_slice(&[vcx.alloc(vir::FieldData {
                        name: name_field,
                        ty: ty_s,
                    })]),
                    snapshot: vir::vir_domain! { vcx; domain [name_s] {
                        function prim_to_snap(Int): [ty_s];
                        function snap_to_prim([ty_s]): Int;
                        axiom_inverse(snap_to_prim, prim_to_snap, Int);
                    } },
                    predicate: Self::mk_simple_predicate(vcx, name_p, name_field),
                    other_predicates: &[],
                    unreachable_to_snap: Self::mk_unreachable(vcx, unreachable_to_snap, ty_s),
                    function_snap: Self::mk_snap(vcx, ref_to_pred, ref_to_snap, Some(name_field), ty_s),
                    //method_refold: mk_refold(vcx, name_p, ty_s),
                    field_projection_p: &[],
                    method_assign: Self::mk_assign(vcx, ref_to_pred, method_assign, ref_to_snap, ty_s),
                }, ()))
            }

            TyKind::Tuple(tys) => {
                let field_ty_out = tys
                    .iter()
                    .map(|ty| deps.require_ref::<crate::encoders::TypeEncoder>(ty).unwrap())
                    .collect::<Vec<_>>();
                // TODO: name the tuple according to its types, or make generic?
                let tmp_ty_name: String = field_ty_out.iter().map(|e| format!("_{}", e.snapshot.get_domain().unwrap())).collect();

                Ok((Self::mk_structlike(
                    vcx,
                    deps,
                    task_key,
                    vir::vir_format!(vcx, "s_Tuple{}{tmp_ty_name}", tys.len()),
                    vir::vir_format!(vcx, "p_Tuple{}{tmp_ty_name}", tys.len()),
                    field_ty_out,
                )?, ()))
            }

            TyKind::Param(_param) => {
                let param_out = deps.require_ref::<crate::encoders::GenericEncoder>(()).unwrap();
                let ty_s = vcx.alloc(vir::TypeData::Domain(param_out.snapshot_param_name));
                let ref_to_pred = Self::mk_predicate_ident(param_out.predicate_param_name);
                let ref_to_snap = Self::mk_function_snap_identifier(vcx, param_out.predicate_param_name, ty_s);
                let unreachable_to_snap = Self::mk_function_unreachable_identifier(vcx, param_out.snapshot_param_name);
                let method_assign = Self::mk_function_assign(vcx, param_out.predicate_param_name, ty_s);
                deps.emit_output_ref::<Self>(*task_key, TypeEncoderOutputRef {
                    ref_to_pred,
                    snapshot: ty_s,
                    unreachable_to_snap,
                    ref_to_snap,
                    //method_refold: "refold_p_Param",
                    specifics: TypeEncoderOutputRefSub::Param,
                    method_assign,
                });
                Ok((TypeEncoderOutput {
                    fields: &[],
                    snapshot: vir::vir_domain! { vcx; domain s_ParamTodo { // TODO: should not be emitted -- make outputs vectors
                    } },
                    predicate: vir::vir_predicate! { vcx; predicate p_ParamTodo(self_p: Ref) },
                    other_predicates: &[],
                    unreachable_to_snap: Self::mk_unreachable(vcx, unreachable_to_snap, ty_s),
                    function_snap: Self::mk_snap(vcx, ref_to_pred, ref_to_snap, None, ty_s),
                    //method_refold: mk_refold(vcx, param_out.predicate_param_name, ty_s),
                    field_projection_p: &[],
                    method_assign: Self::mk_assign(vcx, ref_to_pred, method_assign, ref_to_snap, ty_s),
                }, ()))
            }
            TyKind::Adt(adt_def, substs) if adt_def.is_struct() => {
                println!("encoding ADT {adt_def:?} with substs {substs:?}");
                let substs = ty::List::identity_for_item(vcx.tcx, adt_def.did());
                let field_ty_out = adt_def.all_fields()
                    .map(|field| deps.require_ref::<crate::encoders::TypeEncoder>(field.ty(vcx.tcx, substs)).unwrap())
                    .collect::<Vec<_>>();
                let did_name = vcx.tcx.item_name(adt_def.did()).to_ident_string();

                Ok((Self::mk_structlike(
                    vcx,
                    deps,
                    task_key,
                    vir::vir_format!(vcx, "s_Adt_{did_name}"),
                    vir::vir_format!(vcx, "p_Adt_{did_name}"),
                    field_ty_out,
                )?, ()))
            }
            TyKind::Adt(adt_def, substs) if adt_def.is_enum() => {
                Ok((Self::mk_enum(vcx, deps, *adt_def, task_key)?, ()))
            }
            TyKind::Never => {
                let ty_s = vcx.alloc(vir::TypeData::Domain("s_Never"));
                let ref_to_pred = Self::mk_predicate_ident("p_Never");
                let ref_to_snap = Self::mk_function_snap_identifier(vcx, "p_Never", ty_s);
                let unreachable_to_snap = Self::mk_function_unreachable_identifier(vcx, "s_Never");
                let method_assign = Self::mk_function_assign(vcx, "p_Never", ty_s);
                let specifics = TypeEncoderOutputRefSub::EnumLike(TypeEncoderOutputRefSubEnum {
                    field_discriminant: "FIXME", // FIXME
                    snap_to_disc_snap: FunctionIdent::new("FIXME", UnaryArity::new([ty_s])), // FIXME
                    variants: &[],
                });
                deps.emit_output_ref::<Self>(*task_key, TypeEncoderOutputRef {
                    ref_to_pred,
                    snapshot: ty_s,
                    unreachable_to_snap,
                    ref_to_snap,
                    //method_refold: "refold_p_Never",
                    specifics,
                    method_assign,
                });
                Ok((TypeEncoderOutput {
                    fields: vcx.alloc_slice(&[vcx.alloc(vir::FieldData {
                        name: vir::vir_format!(vcx, "f_Never"),
                        ty: ty_s,
                    })]),
                    snapshot: vir::vir_domain! { vcx; domain s_Never {} },
                    predicate: vir::vir_predicate! { vcx; predicate p_Never(self_p: Ref) },
                    other_predicates: &[],
                    unreachable_to_snap: Self::mk_unreachable(vcx, unreachable_to_snap, ty_s),
                    function_snap: Self::mk_snap(vcx, ref_to_pred, ref_to_snap, None, ty_s),
                    //method_refold: mk_refold(vcx, "p_Never", ty_s),
                    field_projection_p: &[],
                    method_assign: Self::mk_assign(vcx, ref_to_pred, method_assign, ref_to_snap, ty_s),
                }, ()))
            }
            //_ => Err((TypeEncoderError::UnsupportedType, None)),
            unsupported_type => todo!("type not supported: {unsupported_type:?}"),
        })
    }
}

impl TypeEncoder {
    fn get_bit_width(tcx: ty::TyCtxt, ty: ty::Ty) -> u64 {
        let pointer_size = tcx.data_layout.pointer_size.bits() as u32;
        match ty.kind() {
            // TODO: maybe we don't want to use the target architecture bit-width when verifying?
            ty::TyKind::Int(ty) => ty.normalize(pointer_size).bit_width().unwrap(),
            ty::TyKind::Uint(ty) => ty.normalize(pointer_size).bit_width().unwrap(),
            kind => unreachable!("tried to get bit width of non-integer type {kind:?}"),
        }
    }

    fn mk_unreachable<'vir, 'tcx>(
        vcx: &'vir vir::VirCtxt<'tcx>,
        unreachable_fn: FunctionIdent<'vir, NullaryArity>,
        snapshot_ty: vir::Type<'vir>,
    ) -> vir::Function<'vir> {
        vcx.mk_function(
            unreachable_fn.name(),
            &[],
            snapshot_ty,
            vcx.alloc_slice(&[vcx.mk_todo_expr("false")]),
            &[],
            None
        )
    }

    fn mk_enum<'tcx, 'vir>(
        vcx: &'vir vir::VirCtxt<'tcx>,
        deps: &mut TaskEncoderDependencies<'vir>,
        adt: ty::AdtDef<'tcx>,
        task_key: &<TypeEncoder as TaskEncoder>::TaskKey<'tcx>,
    ) -> Result<
        <TypeEncoder as TaskEncoder>::OutputFullLocal<'vir>,
        (
            <TypeEncoder as TaskEncoder>::EncodingError,
            Option<<TypeEncoder as TaskEncoder>::OutputFullDependency<'vir>>,
        ),
    > {
        let did_name = vcx.tcx.item_name(adt.did()).to_ident_string();

        let name_s = vir::vir_format!(vcx, "s_Adt_{did_name}");
        let name_p = vir::vir_format!(vcx, "p_Adt_{did_name}");

        let field_discriminant = vir::vir_format!(vcx, "p_Adt_{did_name}_discriminant");

        let ty_s = vcx.alloc(vir::TypeData::Domain(name_s));

        let s_discr_func_name = vir::vir_format!(vcx, "{name_s}_discriminant");

        let discr_type = adt.repr().discr_type().to_ty(vcx.tcx);
        let discr_type = deps.require_ref::<crate::encoders::TypeEncoder>(discr_type).unwrap();

        let mut variants = Vec::new();

        for (idx, variant) in adt.variants().iter_enumerated() {
            let name_s =
                vir::vir_format!(vcx, "s_Adt_{did_name}_{idx:?}_{}", variant.name.as_str());
            let name_p =
                vir::vir_format!(vcx, "p_Adt_{did_name}_{idx:?}_{}", variant.name.as_str());

            // TODO dedup with the mk_enum_variant code
            let substs = ty::List::identity_for_item(vcx.tcx, variant.def_id);

            let fields = variant
                .fields
                .iter()
                .map(|field| {
                    deps.require_ref::<crate::encoders::TypeEncoder>(field.ty(vcx.tcx, substs))
                        .unwrap()
                })
                .collect::<Vec<_>>();

            let snapshot_constructor_args = vcx.alloc_slice(
                &fields
                    .iter()
                    .map(|field_ty_out| field_ty_out.snapshot)
                    .collect::<Vec<_>>(),
            );

            let field_snaps_to_snap = Self::mk_from_fields(vcx, name_s, snapshot_constructor_args);

            let field_access = Self::mk_field_access_functions(&fields, vcx, name_p, name_s, ty_s);

            let ref_sub_struct = TypeEncoderOutputRefSubStruct {
                field_snaps_to_snap,
                field_access,
            };

            variants.push((ref_sub_struct, Self::mk_predicate_ident(name_p)));
        }

        let unreachable_to_snap = Self::mk_function_unreachable_identifier(vcx, name_s);
        let ref_to_snap = Self::mk_function_snap_identifier(vcx, name_p, ty_s);
        let method_assign = Self::mk_function_assign(vcx, name_p, ty_s);

        let snap_to_disc_snap = FunctionIdent::new(s_discr_func_name, UnaryArity::new([ty_s]));

        deps.emit_output_ref::<TypeEncoder>(
            *task_key,
            TypeEncoderOutputRef {
                snapshot: ty_s,
                specifics: TypeEncoderOutputRefSub::EnumLike(TypeEncoderOutputRefSubEnum {
                    field_discriminant,
                    snap_to_disc_snap,
                    variants: vcx.alloc(variants),
                }),
                method_assign,
                ref_to_pred: Self::mk_predicate_ident(name_p),
                ref_to_snap,
                unreachable_to_snap,
            },
        );

        let mut funcs: Vec<vir::DomainFunction<'vir>> = vec![];
        let mut axioms: Vec<vir::DomainAxiom<'vir>> = vec![];
        let mut field_projection_p = Vec::new();
        let mut other_predicates = Vec::new();

        funcs.push(vcx.alloc(vir::DomainFunctionData {
            unique: false,
            name: s_discr_func_name,
            args: vcx.alloc_slice(&[ty_s]),
            ret: discr_type.snapshot,
        }));

        let mut predicate_accumulator = vcx.mk_bool::<false>();

        let self_local = vcx.mk_local_ex("self_p");

        let discr_field_access = vcx.mk_field_expr(self_local, field_discriminant);
        let mut snap_accumulator = unreachable_to_snap.apply(vcx, []);

        for (vidx, discr) in adt.discriminants(vcx.tcx) {
            let variant = adt.variant(vidx);
            let name_s =
                vir::vir_format!(vcx, "s_Adt_{did_name}_{vidx:?}_{}", variant.name.as_str());
            let name_p =
                vir::vir_format!(vcx, "p_Adt_{did_name}_{vidx:?}_{}", variant.name.as_str());

            let ref_to_pred = Self::mk_predicate_ident(name_p);
            let discr_ty = deps.require_ref::<crate::encoders::TypeEncoder>(discr.ty).unwrap();
            let idx_expr = discr_ty.expr_from_u128(discr.val);

            let (_, cons_call) = Self::mk_enum_variant(
                vcx,
                deps,
                variant,
                vidx,
                idx_expr,
                ty_s,
                name_s,
                name_p,
                ref_to_pred,
                snap_to_disc_snap,
                &mut funcs,
                &mut field_projection_p,
                &mut axioms,
                &mut other_predicates,
            );

            let cond = vcx.mk_bin_op_expr(vir::BinOpKind::CmpEq, discr_field_access, idx_expr);

            let pred_call = vcx.alloc(vir::ExprData::PredicateApp(ref_to_pred.apply(vcx, [self_local])));
            predicate_accumulator =
                vcx.mk_ternary_expr(cond, pred_call, predicate_accumulator);

            snap_accumulator = vcx.mk_ternary_expr(cond, cons_call, snap_accumulator)
        }

        let variants_len = vcx.mk_const_expr(vir::ConstData::Int(adt.variants().len() as u128));

        let predicate = {
            let acc = vcx.mk_acc_field_expr(self_local, field_discriminant);
            let discr_field_access_int = discr_type.expect_prim().snap_to_prim.apply(vcx, [discr_field_access]);

            // TODO: handle the empty enum? i guess the lower and upper bound together for an empty enum are false which is correct?
            let disc_lower_bound = vcx.mk_bin_op_expr(
                vir::BinOpKind::CmpGe,
                discr_field_access_int,
                vcx.mk_int::<0>(),
            );

            let disc_upper_bound = vcx.mk_bin_op_expr(
                vir::BinOpKind::CmpLt,
                discr_field_access_int,
                variants_len,
            );

            let expr = Some(vcx.mk_conj(&[
                acc,
                disc_lower_bound,
                disc_upper_bound,
                predicate_accumulator,
            ]));
            vcx.mk_predicate(name_p, vcx.alloc_slice(&[vcx.mk_local_decl("self_p", &vir::TypeData::Ref)]), expr)
        };
        let ref_to_pred = Self::mk_predicate_ident(name_p);

        let pred_app = ref_to_pred.apply(vcx, [self_local]);

        let function_snap = vcx.mk_function(
            vir::vir_format!(vcx, "{name_p}_snap"),
            vcx.alloc_slice(&[vcx.mk_local_decl("self_p", &vir::TypeData::Ref)]),
            ty_s,
            vcx.alloc_slice(&[vcx.alloc(vir::ExprData::PredicateApp(pred_app))]),
            &[],
            Some(vcx.mk_unfolding_expr(pred_app, snap_accumulator)),
        );

        // discriminant bounds axiom
        {
            let self_local = vcx.mk_local_ex("self");
            let discr_func_call = snap_to_disc_snap.apply(vcx, [self_local]);
            let discr_func_call_int = discr_type.expect_prim().snap_to_prim.apply(vcx, [discr_func_call]);
            let body1 = vcx.mk_bin_op_expr(
                vir::BinOpKind::CmpGe,
                discr_func_call_int,
                vcx.mk_int::<0>(),
            );

            let body2 = vcx.mk_bin_op_expr(
                vir::BinOpKind::CmpLt,
                discr_func_call_int,
                variants_len,
            );

            let body = vcx.mk_bin_op_expr(vir::BinOpKind::And, body1, body2);

            axioms.push(vcx.mk_domain_axiom(
                vir::vir_format!(vcx, "ax_{name_s}_discriminant_bounds"),
                vcx.mk_forall_expr(
                    vcx.alloc_slice(&[vcx.mk_local_decl("self", ty_s)]),
                    &[],
                    body,
                ),
            ));
        }

        let method_assign = Self::mk_function_assign(vcx, name_p, ty_s);

        Ok(TypeEncoderOutput {
            fields: vcx.alloc_slice(&[vcx.alloc(vir::FieldData {
                ty: discr_type.snapshot, 
                name: field_discriminant,
            })]),
            snapshot: vir::vir_domain! { vcx; domain [name_s] {
                with_funcs [funcs];
                with_axioms [axioms];
            } },
            predicate,
            other_predicates: vcx.alloc_slice(&other_predicates),
            function_snap,
            //method_refold: mk_refold(vcx, name_p, ty_s),
            field_projection_p: vcx.alloc_slice(&field_projection_p),
            method_assign: Self::mk_assign(vcx, ref_to_pred, method_assign, ref_to_snap, ty_s),
            unreachable_to_snap: Self::mk_unreachable(vcx, unreachable_to_snap, ty_s),
        })
    }

    fn mk_enum_variant<'vir, 'tcx>(
        vcx: &'vir vir::VirCtxt<'tcx>,
        deps: &mut TaskEncoderDependencies<'vir>,
        variant: &ty::VariantDef,
        variant_idx: abi::VariantIdx,
        variant_idx_expr: vir::Expr<'vir>,
        ty_s: &'vir vir::TypeData<'vir>,
        name_s: &'vir str,
        name_p: &'vir str,
        ref_to_pred: PredicateIdent<'vir, UnaryArity<'vir>>,
        snap_to_disc_snap: FunctionIdent<'vir, UnaryArity<'vir>>,
        funcs: &mut Vec<&'vir vir::DomainFunctionData<'vir>>,
        field_projection_p: &mut Vec<&'vir vir::FunctionData<'vir>>,
        axioms: &mut Vec<vir::DomainAxiom<'vir>>,
        predicates: &mut Vec<&'vir vir::PredicateData<'vir>>,
    ) -> (&'vir vir::PredicateAppData<'vir>, &'vir vir::ExprData<'vir>) {
        let substs = ty::List::identity_for_item(vcx.tcx, variant.def_id);
        let fields = variant
            .fields
            .iter()
            .map(|field| {
                deps.require_ref::<crate::encoders::TypeEncoder>(field.ty(vcx.tcx, substs))
                    .unwrap()
            })
            .collect::<Vec<_>>();

        let snapshot_constructor_args = vcx.alloc_slice(
            &fields
                .iter()
                .map(|field_ty_out| field_ty_out.snapshot)
                .collect::<Vec<_>>(),
        );

        let field_snaps_to_snap = Self::mk_from_fields(vcx, name_s, snapshot_constructor_args);

        let field_access = Self::mk_field_access_functions(&fields, vcx, name_p, name_s, ty_s);

        Self::mk_field_projection_p(vcx, &field_access, &fields, funcs, ty_s, field_projection_p);

        let cons_name = vir::vir_format!(vcx, "{name_s}_cons");
        funcs.push(
            vcx.alloc(vir::DomainFunctionData {
                unique: false,
                name: cons_name,
                args: vcx.alloc_slice(
                    &fields
                        .iter()
                        .map(|field| field.snapshot)
                        .collect::<Vec<_>>(),
                ),
                ret: ty_s,
            }),
        );

        Self::mk_cons_read_axioms(
            vcx,
            &fields,
            field_snaps_to_snap,
            field_access,
            axioms,
            name_s,
        );

        if !fields.is_empty() {
            axioms.push(Self::mk_cons_axiom(
                vcx,
                field_snaps_to_snap,
                &fields,
                field_access,
                ty_s,
                name_s,
            ));
        }

        // discriminant of constructor matches the variant idx
        {
            let (cons_qvars, cons_args, cons_call) =
                Self::cons_read_parts(vcx, &fields, field_snaps_to_snap);

            let body = vcx.mk_bin_op_expr(vir::BinOpKind::CmpEq, 
                snap_to_disc_snap.apply(vcx, [cons_call]),
                variant_idx_expr,
            );

            let ax = if fields.is_empty() {
                body
            } else {
                // only apply the forall if there are fields
                vcx.mk_forall_expr(
                    cons_qvars,
                    vcx.alloc_slice(&[vcx.alloc_slice(&[cons_call])]),
                    body,
                )
            };

            axioms.push(vcx.mk_domain_axiom(vir::vir_format!(vcx, "ax_{name_s}_cons_{variant_idx:?}_discr"), ax));
        }

        Self::mk_read_write_axioms(vcx, &fields, field_access, axioms, ty_s, name_s);

        // discriminant of write call stays the same
        for (write_idx, write_ty_out) in fields.iter().enumerate() {
            let qvars = vcx.alloc_slice(&[
                vcx.mk_local_decl("self", ty_s),
                vcx.mk_local_decl("val", write_ty_out.snapshot),
            ]);

            let write_func: FunctionIdent<'vir, BinaryArity<'vir>> = FunctionIdent::new(
                vir::vir_format!(vcx, "{name_s}_write_{write_idx}"),
                BinaryArity::new([ty_s, write_ty_out.snapshot]),
            );

            let write_call =
                write_func.apply(vcx, [vcx.mk_local_ex("self"), vcx.mk_local_ex("val")]);

            let discriminant_of_write = snap_to_disc_snap.apply(vcx, [write_call]);

            axioms.push(vcx.mk_domain_axiom(
                vir::vir_format!(vcx, "ax_{name_s}_discriminant_write_{write_idx}"),
                vcx.mk_forall_expr(
                    qvars,
                    vcx.alloc_slice(&[vcx.alloc_slice(&[discriminant_of_write])]),
                    vcx.mk_bin_op_expr(vir::BinOpKind::CmpEq, discriminant_of_write, variant_idx_expr),
                ),
            ));
        }

        predicates.push(Self::mk_structlike_predicate(vcx, &fields, field_access, name_p));

        Self::mk_structlike_snap_parts(vcx, ref_to_pred, field_snaps_to_snap, &fields, field_access)
    }

    fn mk_simple_predicate<'vir, 'tcx>(
        vcx: &'vir vir::VirCtxt<'tcx>,
        predicate_name: &'vir str,
        field_name: &'vir str,
    ) -> vir::Predicate<'vir> {
        let predicate_body = vcx.mk_acc_field_expr(vcx.mk_local_ex("self_p"), field_name);
        vir::vir_predicate! { vcx; predicate [predicate_name](self_p: Ref) { [predicate_body] } }
    }
    /*
    fn mk_refold<'vir>(
        vcx: &'vir vir::VirCtxt<'vir>,
        predicate_name: &'vir str,
        snapshot_ty: vir::Type<'vir>,
    ) -> vir::Method<'vir> {
        vcx.alloc(vir::MethodData {
            name: vir::vir_format!(vcx, "refold_{predicate_name}"),
            args: vcx.alloc_slice(&[
                vcx.alloc(vir::LocalDeclData {
                    name: "_p",
                    ty: vcx.alloc(vir::TypeData::Ref),
                }),
                vcx.alloc(vir::LocalDeclData {
                    name: "_s_old",
                    ty: snapshot_ty,
                }),
                vcx.alloc(vir::LocalDeclData {
                    name: "_s_new",
                    ty: snapshot_ty,
                }),
            ]),
            rets: &[],
            pres: vcx.alloc_slice(&[
                vcx.alloc(vir::ExprData::PredicateApp(vcx.alloc(vir::PredicateAppData {
                    target: predicate_name,
                    args: vcx.alloc_slice(&[
                        vcx.mk_local_ex("_p"),
                        vcx.mk_local_ex("_s_old"),
                    ]),
                }))),
            ]),
            posts: vcx.alloc_slice(&[
                vcx.alloc(vir::ExprData::PredicateApp(vcx.alloc(vir::PredicateAppData {
                    target: predicate_name,
                    args: vcx.alloc_slice(&[
                        vcx.mk_local_ex("_p"),
                        vcx.mk_local_ex("_s_new"),
                    ]),
                }))),
            ]),
            blocks: None,
        })
    }
    */
    // TODO: there is a lot of duplication here, both in these assign/
    //   reassign methods, and in the match cases below
    //   also: is mk_assign really worth it? (used in constant method
    //   arguments only)
    fn mk_assign<'vir, 'tcx>(
        vcx: &'vir vir::VirCtxt<'tcx>,
        ref_to_pred: PredicateIdent<'vir, UnaryArity<'vir>>,
        assign_fn: MethodIdent<'vir, BinaryArity<'vir>>,
        snapshot_fn: FunctionIdent<'vir, UnaryArity<'vir>>,
        snapshot_ty: vir::Type<'vir>,
    ) -> vir::Method<'vir> {
        vcx.mk_method(
            assign_fn.name(),
            vcx.alloc_slice(&[
                vcx.alloc(vir::LocalDeclData {
                    name: "_p",
                    ty: &vir::TypeData::Ref,
                }),
                vcx.alloc(vir::LocalDeclData {
                    name: "_s_new",
                    ty: snapshot_ty,
                }),
            ]),
            &[],
            &[],
            vcx.alloc_slice(&[
                vcx.alloc(vir::ExprData::PredicateApp(ref_to_pred.apply(vcx, [vcx.mk_local_ex("_p")]))),
                vcx.mk_bin_op_expr(
                    vir::BinOpKind::CmpEq,
                    snapshot_fn.apply(vcx, [vcx.mk_local_ex("_p")]),
                    vcx.mk_local_ex("_s_new")
                ),
            ]),
            None
        )
    }

    fn mk_predicate_ident<'vir>(
        name_p: &'vir str,
    ) -> PredicateIdent<'vir, UnaryArity<'vir>> {
        PredicateIdent::new(
            name_p,
            UnaryArity::new([&vir::TypeData::Ref]),
        )
    }

    fn mk_from_fields<'tcx, 'vir>(
        vcx: &'vir vir::VirCtxt<'tcx>,
        name_s: &'vir str,
        args: &'vir [vir::Type<'vir>],
    ) -> FunctionIdent<'vir, UnknownArity<'vir>> {
        FunctionIdent::new(
            vir::vir_format!(vcx, "{name_s}_cons"),
            UnknownArity::new(args)
        )
    }

    fn mk_function_snap_identifier<'tcx, 'vir>(
        vcx: &'vir vir::VirCtxt<'tcx>,
        name_p: &'vir str,
        ty: vir::Type<'vir>
    ) -> FunctionIdent<'vir, UnaryArity<'vir>> {
        FunctionIdent::new(
            vir::vir_format!(vcx, "{name_p}_snap"),
            UnaryArity::new([ty]),
        )
    }

    fn mk_primitive<'tcx, 'vir>(
        vcx: &'vir vir::VirCtxt<'tcx>,
        name_s: &'vir str,
        ty_s: vir::Type<'vir>,
        ty_prim: vir::Type<'vir>,
    ) -> (FunctionIdent<'vir, UnaryArity<'vir>>, FunctionIdent<'vir, UnaryArity<'vir>>) {
        let val = FunctionIdent::new(
            vir::vir_format!(vcx, "{name_s}_val"),
            UnaryArity::new([ty_s]),
        );
        let prim = FunctionIdent::new(
            vir::vir_format!(vcx, "{name_s}_cons"),
            UnaryArity::new([ty_prim]),
        );
        (val, prim)
    }

    fn mk_function_unreachable_identifier<'tcx, 'vir>(
        vcx: &'vir vir::VirCtxt<'tcx>,
        name_s: &'vir str,
    ) -> FunctionIdent<'vir, NullaryArity> {
        FunctionIdent::new(
            vir::vir_format!(vcx, "{name_s}_unreachable"),
            NullaryArity::new([]),
        )
    }

    fn mk_function_assign<'tcx, 'vir>(
        vcx: &'vir vir::VirCtxt<'tcx>,
        name_p: &'vir str,
        snapshot_ty: vir::Type<'vir>,
    ) -> MethodIdent<'vir, BinaryArity<'vir>> {
        MethodIdent::new(
            vir::vir_format!(vcx, "assign_{name_p}"),
            BinaryArity::new([&vir::TypeData::Ref, snapshot_ty]),
        )
    }

    fn mk_function_field_projection<'tcx, 'vir>(
        vcx: &'vir vir::VirCtxt<'tcx>,
        name_p: &'vir str,
        name_s: &'vir str,
        idx: usize,
        ty_s: vir::Type<'vir>,
        field_ty_s: vir::Type<'vir>,
    ) -> FieldAccessFunctions<'vir> {
        let read = vir::vir_format!(vcx, "{name_s}_read_{idx}");
        let read = FunctionIdent::new(
            &read,
            UnaryArity::new([ty_s]),
        );
        let write = vir::vir_format!(vcx, "{name_s}_write_{idx}");
        let write = FunctionIdent::new(
            &write,
            BinaryArity::new([ty_s, field_ty_s]),
        );
        let projection_p = vir::vir_format!(vcx, "{name_p}_field_{idx}");
        let projection_p = FunctionIdent::new(
            &projection_p,
            UnaryArity::new([&vir::TypeData::Ref]),
        );
        FieldAccessFunctions {
            read,
            write,
            projection_p,
        }
    }

    fn mk_field_access_functions<'vir, 'tcx>(
        field_ty_out: &[TypeEncoderOutputRef<'vir>],
        vcx: &'vir vir::VirCtxt<'tcx>,
        name_p: &'vir str,
        name_s: &'vir str,
        ty_s: &'vir vir::TypeData<'vir>,
    ) -> &'vir [FieldAccessFunctions<'vir>] {
        let mut field_access = Vec::new();
        for idx in 0..field_ty_out.len() {
            field_access.push(Self::mk_function_field_projection(
                vcx,
                name_p,
                name_s,
                idx,
                ty_s,
                field_ty_out[idx].snapshot,
            ));
        }
        vcx.alloc_slice(&field_access)
    }

    fn mk_snap<'vir, 'tcx>(
        vcx: &'vir vir::VirCtxt<'tcx>,
        predicate: PredicateIdent<'vir, UnaryArity<'vir>>,
        snapshot_fn: FunctionIdent<'vir, UnaryArity<'vir>>,
        field_name: Option<&'vir str>,
        snapshot_ty: vir::Type<'vir>,
    ) -> vir::Function<'vir> {
        let self_ = vcx.mk_local_ex("self");
        let pred_app = predicate.apply(vcx, [self_]);
        vcx.mk_function(
            snapshot_fn.name(),
            vcx.alloc_slice(&[
                vcx.mk_local_decl("self", &vir::TypeData::Ref),
            ]),
            snapshot_ty,
            vcx.alloc_slice(&[
                vcx.mk_predicate_app_expr(pred_app),
            ]),
            &[],
            field_name.map(|field_name|
                vcx.mk_unfolding_expr(pred_app, vcx.mk_field_expr(self_, field_name))
            )
        )
    }
    fn mk_structlike<'tcx, 'vir>(
        vcx: &'vir vir::VirCtxt<'tcx>,
        deps: &mut TaskEncoderDependencies<'vir>,
        task_key: &<TypeEncoder as TaskEncoder>::TaskKey<'tcx>,
        name_s: &'vir str,
        name_p: &'vir str,
        field_ty_out: Vec<TypeEncoderOutputRef<'vir>>,
    ) -> Result<<TypeEncoder as TaskEncoder>::OutputFullLocal<'vir>, (
        <TypeEncoder as TaskEncoder>::EncodingError,
        Option<<TypeEncoder as TaskEncoder>::OutputFullDependency<'vir>>,
    )> {
        let ty_s = vcx.alloc(vir::TypeData::Domain(name_s));

        let field_access = Self::mk_field_access_functions(&field_ty_out, vcx, name_p, name_s, ty_s);

        let snapshot_constructor_args =
            vcx.alloc_slice(&field_ty_out.iter()
                    .map(|field_ty_out| field_ty_out.snapshot)
                    .collect::<Vec<_>>());

        let ref_to_pred = Self::mk_predicate_ident(name_p);
        let ref_to_snap = Self::mk_function_snap_identifier(vcx, name_p, ty_s);
        let field_snaps_to_snap = Self::mk_from_fields(vcx, name_s, snapshot_constructor_args);
        let unreachable_to_snap = Self::mk_function_unreachable_identifier(vcx, name_s);
        let method_assign = Self::mk_function_assign(vcx, name_p, ty_s);
        deps.emit_output_ref::<TypeEncoder>(*task_key, TypeEncoderOutputRef {
            ref_to_pred,
            snapshot: vcx.alloc(vir::TypeData::Domain(name_s)),
            unreachable_to_snap,
            ref_to_snap,
            //method_refold: vir::vir_format!(vcx, "refold_{name_p}"),
            specifics: TypeEncoderOutputRefSub::StructLike(TypeEncoderOutputRefSubStruct {
                field_snaps_to_snap,
                field_access,
            }),
            method_assign,
        });

        let mut funcs: Vec<vir::DomainFunction<'vir>> = vec![];
        let mut axioms: Vec<vir::DomainAxiom<'vir>> = vec![];

        let cons_name = field_snaps_to_snap.name();
        funcs.push(vcx.alloc(vir::DomainFunctionData {
            unique: false,
            name: cons_name,
            args: snapshot_constructor_args,
            ret: ty_s,
        }));

        let mut field_projection_p = Vec::new();
        Self::mk_field_projection_p(
            vcx,
            field_access,
            &field_ty_out,
            &mut funcs,
            ty_s,
            &mut field_projection_p,
        );
        let field_projection_p = vcx.alloc_slice(&field_projection_p);

        Self::mk_read_write_axioms(vcx, &field_ty_out, field_access, &mut axioms, ty_s, name_s);

        // constructor
        {
            Self::mk_cons_read_axioms(
                vcx,
                &field_ty_out,
                field_snaps_to_snap,
                field_access,
                &mut axioms,
                name_s,
            );

            if !field_ty_out.is_empty() {
                axioms.push(Self::mk_cons_axiom(
                    vcx,
                    field_snaps_to_snap,
                    &field_ty_out,
                    field_access,
                    ty_s,
                    name_s,
                ));
            }
        }

        // predicate
        let predicate = Self::mk_structlike_predicate(vcx, &field_ty_out, field_access, name_p);

        let function_snap = Self::mk_structlike_snap(
            vcx,
            ref_to_pred,
            ref_to_snap,
            ty_s,
            field_snaps_to_snap,
            &field_ty_out,
            field_access,
        );

        Ok(TypeEncoderOutput {
            fields: &[],
            snapshot: vir::vir_domain! { vcx; domain [name_s] {
                with_funcs [funcs];
                with_axioms [axioms];
            } },
            predicate,
            other_predicates: &[],
            unreachable_to_snap: Self::mk_unreachable(vcx, unreachable_to_snap, ty_s),
            function_snap,
            //method_refold: mk_refold(vcx, name_p, ty_s),
            field_projection_p,
            method_assign: Self::mk_assign(vcx, ref_to_pred, method_assign, ref_to_snap, ty_s),
        })
    }

    fn mk_structlike_snap<'vir, 'tcx>(
        vcx: &'vir vir::VirCtxt<'tcx>,
        ref_to_pred: PredicateIdent<'vir, vir::KnownArity<'vir, 1>>,
        ref_to_snap: FunctionIdent<'vir, vir::KnownArity<'vir, 1>>,
        ty_s: &'vir vir::TypeData<'vir>,
        field_snaps_to_snap: FunctionIdent<'vir, UnknownArity<'vir>>,
        field_ty_out: &[TypeEncoderOutputRef<'vir>],
        field_access: &[FieldAccessFunctions<'vir>],
    ) -> &'vir vir::FunctionData<'vir> {
        let (pred_app, expr) =
            Self::mk_structlike_snap_parts(vcx, ref_to_pred, field_snaps_to_snap, field_ty_out, field_access);

        vcx.mk_function(
            ref_to_snap.name(),
            vcx.alloc_slice(&[vcx.mk_local_decl("self_p", &vir::TypeData::Ref)]),
            ty_s,
            vcx.alloc_slice(&[ vcx.mk_predicate_app_expr(pred_app)]),
            &[],
            Some(expr)
        )
    }

    fn mk_structlike_snap_parts<'vir, 'tcx>(
        vcx: &'vir vir::VirCtxt<'tcx>,
        ref_to_pred: PredicateIdent<'vir, vir::KnownArity<'vir, 1>>,
        field_snaps_to_snap: FunctionIdent<'vir, UnknownArity<'vir>>,
        field_ty_out: &[TypeEncoderOutputRef<'vir>],
        field_access: &[FieldAccessFunctions<'vir>],
    ) -> (&'vir vir::PredicateAppData<'vir>, &'vir vir::ExprData<'vir>) {
        let arg = vcx.mk_local_ex("self_p");
        let pred_app = ref_to_pred.apply(vcx, [arg]);
        let expr = vcx.mk_unfolding_expr(
            pred_app,
            field_snaps_to_snap.apply(
                vcx,
                &field_ty_out
                    .iter()
                    .enumerate()
                    .map(|(idx, field_ty_out)| field_ty_out.ref_to_snap.apply(vcx, [
                        field_access[idx].projection_p.apply(vcx, [arg])
                    ]))
                    .collect::<Vec<_>>()
            )
        );
        (pred_app, expr)
    }

    fn mk_structlike_predicate<'vir, 'tcx>(
        vcx: &'vir vir::VirCtxt<'tcx>,
        field_ty_out: &Vec<TypeEncoderOutputRef<'vir>>,
        field_access: &[FieldAccessFunctions<'vir>],
        name_p: &'vir str,
    ) -> &'vir vir::PredicateData<'vir> {
        let expr = (0..field_ty_out.len())
            .map(|idx| vcx.mk_predicate_app_expr(field_ty_out[idx].ref_to_pred.apply(vcx, [field_access[idx].projection_p.apply(vcx, [vcx.mk_local_ex("self_p")])])))
            .reduce(|base, field_expr| vcx.mk_bin_op_expr(vir::BinOpKind::And, base, field_expr))
            .unwrap_or_else(|| vcx.mk_bool::<true>());
        vcx.mk_predicate(
            name_p,
            vcx.alloc_slice(&[
                vcx.mk_local_decl("self_p", &vir::TypeData::Ref),
            ]),
            Some(expr)
        )
    }

    fn mk_read_write_axioms<'vir, 'tcx>(
        vcx: &'vir vir::VirCtxt<'tcx>,
        field_ty_out: &Vec<TypeEncoderOutputRef<'vir>>,
        field_access: &[FieldAccessFunctions<'vir>],
        axioms: &mut Vec<&vir::DomainAxiomData<'vir>>,
        ty_s: &'vir vir::TypeData<'vir>,
        name_s: &'vir str,
    ) {
        for (write_idx, write_ty_out) in field_ty_out.iter().enumerate() {
            for (read_idx, _read_ty_out) in field_ty_out.iter().enumerate() {
                let slf = vcx.mk_local_ex("self");
                let val = vcx.mk_local_ex("val");
                let write_read = field_access[read_idx].read.apply(vcx, [
                    field_access[write_idx].write.apply(vcx, [slf, val]),
                ]);
                let rhs = if read_idx == write_idx {
                    val
                } else {
                    field_access[read_idx].read.apply(vcx, [slf])
                };
                axioms.push(
                    vcx.mk_domain_axiom(
                        vir::vir_format!(vcx, "ax_{name_s}_write_{write_idx}_read_{read_idx}"),
                        vcx.mk_forall_expr(
                            vcx.alloc_slice(&[
                                vcx.mk_local_decl("self", ty_s),
                                vcx.mk_local_decl("val", write_ty_out.snapshot),
                            ]),
                            vcx.alloc_slice(&[vcx.alloc_slice(&[write_read])]),
                            vcx.mk_bin_op_expr(vir::BinOpKind::CmpEq, write_read, rhs)
                        )
                    )
                );
            }
        }
    }

    fn mk_cons_axiom<'vir, 'tcx>(
        vcx: &'vir vir::VirCtxt<'tcx>,
        field_snaps_to_snap: FunctionIdent<'vir, UnknownArity<'vir>>,
        field_ty_out: &Vec<TypeEncoderOutputRef<'vir>>,
        field_access: &[FieldAccessFunctions<'vir>],
        ty_s: &'vir vir::TypeData<'vir>,
        name_s: &'vir str,
    ) -> &'vir vir::DomainAxiomData<'vir> {

        let cons_call_with_reads = field_snaps_to_snap.apply(vcx,
            &field_ty_out
                .iter()
                .enumerate()
                .map(|(idx, _field_ty_out)|
                    field_access[idx].read.apply(vcx, [vcx.mk_local_ex("self")])
                )
                .collect::<Vec<_>>(),
        );
        vcx.mk_domain_axiom(
            vir::vir_format!(vcx, "ax_{name_s}_cons"),
            vcx.mk_forall_expr(
                vcx.alloc_slice(&[vcx.mk_local_decl("self", ty_s)]),
                vcx.alloc_slice(&[vcx.alloc_slice(&[cons_call_with_reads])]),
                vcx.mk_bin_op_expr(
                    vir::BinOpKind::CmpEq,
                    cons_call_with_reads,
                    vcx.mk_local_ex("self")
                )
            )
        )
    }

    fn mk_cons_read_axioms<'vir, 'tcx>(
        vcx: &'vir vir::VirCtxt<'tcx>,
        field_ty_out: &Vec<TypeEncoderOutputRef<'vir>>,
        field_snaps_to_snap: FunctionIdent<'vir, UnknownArity<'vir>>,
        field_access: &[FieldAccessFunctions<'vir>],
        axioms: &mut Vec<&vir::DomainAxiomData<'vir>>,
        name_s: &'vir str,
    ) {
        let (cons_qvars, cons_args, cons_call) =
            Self::cons_read_parts(vcx, field_ty_out, field_snaps_to_snap);

        for (read_idx, _) in field_ty_out.iter().enumerate() {
            let cons_read = field_access[read_idx].read.apply(vcx, [cons_call]);
            axioms.push(
                vcx.mk_domain_axiom(
                    vir::vir_format!(vcx, "ax_{name_s}_cons_read_{read_idx}"),
                    vcx.mk_forall_expr(
                        cons_qvars,
                        vcx.alloc_slice(&[vcx.alloc_slice(&[ cons_read,])]),
                        vcx.mk_bin_op_expr(vir::BinOpKind::CmpEq, cons_read, cons_args[read_idx])
                    )
                )
            );
        }
    }

    fn cons_read_parts<'vir, 'tcx>(
        vcx: &'vir vir::VirCtxt<'tcx>,
        field_ty_out: &Vec<TypeEncoderOutputRef<'vir>>,
        field_snaps_to_snap: FunctionIdent<'vir, UnknownArity<'vir>>,
    ) -> (
        &'vir [&'vir vir::LocalDeclData<'vir>],
        Vec<&'vir vir::ExprData<'vir>>,
        &'vir vir::ExprData<'vir>,
    ) {
        let cons_qvars = vcx.alloc_slice(
                &field_ty_out.iter()
                .enumerate()
                .map(|(idx, field_ty_out)| vcx.mk_local_decl(
                    vir::vir_format!(vcx, "f{idx}"),
                    field_ty_out.snapshot,
                ))
                .collect::<Vec<_>>());
        let cons_args = field_ty_out.iter()
            .enumerate()
            .map(|(idx, _field_ty_out)| vcx.mk_local_ex(
                vir::vir_format!(vcx, "f{idx}"),
            ))
            .collect::<Vec<_>>();
        let cons_call = field_snaps_to_snap.apply(vcx, &cons_args);
        (cons_qvars, cons_args, cons_call)
    }

    fn mk_field_projection_p<'vir, 'tcx>(
        vcx: &'vir vir::VirCtxt<'tcx>,
        field_access: &'vir [FieldAccessFunctions<'_>],
        field_ty_out: &[TypeEncoderOutputRef<'vir>],
        funcs: &mut Vec<&vir::DomainFunctionData<'vir>>,
        ty_s: &'vir vir::TypeData<'vir>,
        field_projection_p: &mut Vec<&vir::FunctionData<'vir>>,
    ) {
        for (fa, ty_out) in field_access.iter().zip(field_ty_out) {
            let read = fa.read;
            funcs.push(vir::vir_domain_func! { vcx; function read([ty_s]): [ty_out.snapshot] });

            let write = fa.write;
            funcs.push(vir::vir_domain_func! { vcx; function write([ty_s], [ty_out.snapshot]): [ty_s] });

            field_projection_p.push(
                vcx.mk_function(
                    fa.projection_p.name(),
                    vcx.alloc_slice(&[
                        vcx.mk_local_decl("self", &vir::TypeData::Ref),
                    ]),
                    &vir::TypeData::Ref,
                    &[],
                    &[],
                    None
                )
            );
        }
    }
}
