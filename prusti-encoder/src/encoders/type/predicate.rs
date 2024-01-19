use prusti_rustc_interface::{
    middle::ty::{self, TyKind},
    abi,
};
use task_encoder::{
    TaskEncoder,
    TaskEncoderDependencies,
};
use vir::{BinaryArity, UnaryArity, NullaryArity, UnknownArity, FunctionIdent, MethodIdent, PredicateIdent, CallableIdent};

/// Takes a Rust `Ty` and returns various Viper predicates and functions for
/// working with the type.
pub struct PredicateEnc;

#[derive(Clone, Debug)]
pub enum PredicateEncError {
    UnsupportedType,
}

#[derive(Clone, Copy, Debug)]
pub struct PredicateEncDataStruct<'vir> {
    pub snap_data: DomainDataStruct<'vir>,
    /// Ref to self as argument. Returns Ref to field.
    pub ref_to_field_refs: &'vir [FunctionIdent<'vir, UnaryArity<'vir>>],
}

#[derive(Clone, Copy, Debug)]
pub struct PredicateEncDataEnum<'vir> {
    pub discr: vir::Field<'vir>,
    pub discr_prim: DomainDataPrim<'vir>,
    pub discr_bounds: DiscrBounds<'vir>,
    pub snap_to_discr_snap: FunctionIdent<'vir, UnaryArity<'vir>>,
    pub variants: &'vir [PredicateEncDataVariant<'vir>],
}
#[derive(Clone, Copy, Debug)]
pub struct PredicateEncDataVariant<'vir> {
    pub predicate: PredicateIdent<'vir, UnaryArity<'vir>>,
    pub vid: abi::VariantIdx,
    pub discr: vir::Expr<'vir>,
    pub fields: PredicateEncDataStruct<'vir>,
}

#[derive(Clone, Copy, Debug)]
pub struct PredicateEncDataRef<'vir> {
    pub ref_field: vir::Field<'vir>,
    pub perm: Option<vir::Expr<'vir>>,
    pub snap_data: DomainDataStruct<'vir>,
}

#[derive(Clone, Copy, Debug)]
pub enum PredicateEncData<'vir> {
    Primitive(DomainDataPrim<'vir>),
    // structs, tuples
    StructLike(PredicateEncDataStruct<'vir>),
    EnumLike(Option<PredicateEncDataEnum<'vir>>),
    Ref(PredicateEncDataRef<'vir>),
    Param,
}

// TODO: should output refs actually be references to structs...?
#[derive(Clone, Debug)]
pub struct PredicateEncOutputRef<'vir> {
    /// Constructs the Viper predicate application.
    pub ref_to_pred: PredicateIdent<'vir, UnaryArity<'vir>>,
    /// Construct snapshot from Viper predicate.
    pub ref_to_snap: FunctionIdent<'vir, UnaryArity<'vir>>,
    /// Construct snapshot from an unreachable.
    pub unreachable_to_snap: FunctionIdent<'vir, NullaryArity<'vir>>,
    /// Ref as first argument, snapshot as second. Ensures predicate
    /// access to ref with snapshot value.
    pub method_assign: MethodIdent<'vir, BinaryArity<'vir>>,
    /// Always `TypeData::Domain`.
    pub snapshot: vir::Type<'vir>,
    //pub method_refold: &'vir str,
    pub specifics: PredicateEncData<'vir>,
}
impl<'vir> task_encoder::OutputRefAny for PredicateEncOutputRef<'vir> {}

impl<'vir> PredicateEncOutputRef<'vir> {
    pub fn expect_prim(&self) -> DomainDataPrim<'vir> {
        match self.specifics {
            PredicateEncData::Primitive(prim) => prim,
            _ => panic!("expected primitive type"),
        }
    }
    pub fn expect_ref(&self) -> PredicateEncDataRef<'vir> {
        match self.specifics {
            PredicateEncData::Ref(r) => r,
            s => panic!("expected ref type ({s:?})"),
        }
    }
    pub fn get_structlike(&self) -> Option<&PredicateEncDataStruct<'vir>> {
        match &self.specifics {
            PredicateEncData::StructLike(data) => Some(data),
            _ => None,
        }
    }
    pub fn expect_structlike(&self) -> &PredicateEncDataStruct<'vir> {
        self.get_structlike().expect("expected structlike type")
    }
    pub fn get_enumlike(&self) -> Option<&Option<PredicateEncDataEnum<'vir>>> {
        match &self.specifics {
            PredicateEncData::EnumLike(e) => Some(e),
            _ => None,
        }
    }
    pub fn expect_enumlike(&self) -> Option<&PredicateEncDataEnum<'vir>> {
        self.get_enumlike().expect("expected enumlike type").as_ref()
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

    pub fn expect_variant(&self, vid: abi::VariantIdx) -> &PredicateEncDataVariant<'vir> {
        match &self.specifics {
            PredicateEncData::EnumLike(e) => &e.as_ref().unwrap().variants[vid.as_usize()],
            _ => panic!("expected enum type"),
        }
    }
    pub fn expect_pred_variant_opt(&self, vid: Option<abi::VariantIdx>) -> PredicateIdent<'vir, UnaryArity<'vir>> {
        vid.map(|vid| self.expect_variant(vid).predicate).unwrap_or(self.ref_to_pred)
    }
    pub fn expect_variant_opt(&self, vid: Option<abi::VariantIdx>) -> &PredicateEncDataStruct<'vir> {
        match vid {
            None => self.expect_structlike(),
            Some(vid) => &self.expect_enumlike().expect("empty enum").variants[vid.as_usize()].fields,
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

use super::{snapshot::SnapshotEnc, domain::{DomainDataPrim, DomainDataStruct, DomainDataEnum, DiscrBounds}};

impl TaskEncoder for PredicateEnc {
    task_encoder::encoder_cache!(PredicateEnc);

    type TaskDescription<'vir> = ty::Ty<'vir>;

    type OutputRef<'vir> = PredicateEncOutputRef<'vir>;
    type OutputFullLocal<'vir> = PredicateEncOutput<'vir>;
    //type OutputFullDependency<'vir> = PredicateEncOutputDep<'vir>;

    type EncodingError = PredicateEncError;

    fn task_to_key<'vir>(task: &Self::TaskDescription<'vir>) -> Self::TaskKey<'vir> {
        *task
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
        let snap = deps.require_local::<SnapshotEnc>(*task_key).unwrap();
        let mut enc = vir::with_vcx(|vcx| PredicateEncValues::new(vcx, &snap.base_name, snap.snapshot));
        match task_key.kind() {
            TyKind::Bool | TyKind::Char | TyKind::Int(_) | TyKind::Uint(_) | TyKind::Float(_)  => {
                let specifics = PredicateEncData::Primitive(snap.specifics.expect_primitive());
                deps.emit_output_ref::<Self>(*task_key, enc.output_ref(specifics));
                Ok((enc.mk_prim(&snap.base_name), ()))
            }
            TyKind::Param(_param) => {
                deps.emit_output_ref::<Self>(*task_key, enc.output_ref(PredicateEncData::Param));
                Ok((enc.mk_param(), ()))
            }

            TyKind::Tuple(tys) => {
                let snap_data = snap.specifics.expect_structlike();
                let specifics = enc.mk_struct_ref(None, snap_data);
                deps.emit_output_ref::<Self>(*task_key, enc.output_ref(PredicateEncData::StructLike(specifics)));

                let fields: Vec<_> = tys.iter().map(|ty| deps.require_ref::<PredicateEnc>(ty).unwrap()).collect();
                let fields = enc.mk_field_apps(specifics.ref_to_field_refs, fields);
                let fn_snap_body = enc.mk_struct_ref_to_snap_body(None, fields, snap_data.field_snaps_to_snap);
                Ok((enc.mk_struct(fn_snap_body), ()))
            }
            TyKind::Adt(adt, args) => {
                match adt.adt_kind() {
                    ty::AdtKind::Struct => {
                        let snap_data = snap.specifics.expect_structlike();
                        let specifics = enc.mk_struct_ref(None, snap_data);
                        deps.emit_output_ref::<Self>(*task_key, enc.output_ref(PredicateEncData::StructLike(specifics)));

                        let variant = adt.non_enum_variant();
                        let fields: Vec<_> = variant.fields.iter().map(|f| deps.require_ref::<PredicateEnc>(f.ty(enc.tcx(), args)).unwrap()).collect();
                        let fields = enc.mk_field_apps(specifics.ref_to_field_refs, fields);
                        let fn_snap_body = enc.mk_struct_ref_to_snap_body(None, fields, snap_data.field_snaps_to_snap);
                        Ok((enc.mk_struct(fn_snap_body), ()))
                    }
                    ty::AdtKind::Enum => {
                        let specifics = enc.mk_enum_ref(snap.specifics.expect_enumlike());
                        deps.emit_output_ref::<Self>(*task_key, enc.output_ref(PredicateEncData::EnumLike(specifics)));

                        let specifics = specifics.map(|specifics| {
                            let variants: Vec<_> = specifics.variants.iter().map(|data| {
                                (data.vid, adt.variant(data.vid).fields.iter().map(|f| deps.require_ref::<PredicateEnc>(f.ty(enc.tcx(), args)).unwrap()).collect())
                            }).collect();
                            (specifics, variants)
                        });
                        Ok((enc.mk_enum(specifics), ()))
                    }
                    ty::AdtKind::Union => todo!(),
                }
            }
            TyKind::Never => {
                let specifics = enc.mk_enum_ref(snap.specifics.expect_enumlike());
                assert!(specifics.is_none());
                deps.emit_output_ref::<Self>(*task_key, enc.output_ref(PredicateEncData::EnumLike(None)));

                Ok((enc.mk_enum(None), ()))
            }
            &TyKind::Ref(_, inner, m) => {
                let snap_data = snap.specifics.expect_structlike();
                let specifics = enc.mk_ref_ref(snap_data, m.is_mut());
                deps.emit_output_ref::<Self>(*task_key, enc.output_ref(PredicateEncData::Ref(specifics)));

                let inner = deps.require_ref::<PredicateEnc>(inner).unwrap();
                Ok((enc.mk_ref(inner, specifics), ()))

            }
            unsupported_type => todo!("type not supported: {unsupported_type:?}"),
        }
    }
}

struct PredicateEncValues<'vir, 'tcx> {
    vcx: &'vir vir::VirCtxt<'tcx>,
    ref_to_pred: vir::PredicateIdent<'vir, vir::UnaryArity<'vir>>,
    snap_inst: vir::Type<'vir>,
    ref_to_snap: FunctionIdent<'vir, UnaryArity<'vir>>,
    unreachable_to_snap: FunctionIdent<'vir, NullaryArity<'vir>>,
    method_assign: MethodIdent<'vir, BinaryArity<'vir>>,

    self_ex: vir::Expr<'vir>,
    self_pred_read: vir::PredicateApp<'vir>,
    self_decl: &'vir [vir::LocalDecl<'vir>; 1],

    fields: Vec<vir::Field<'vir>>,
    predicates: Vec<vir::Predicate<'vir>>,
    ref_to_field_refs: Vec<vir::Function<'vir>>,
}

impl<'vir, 'tcx> PredicateEncValues<'vir, 'tcx> {
    // Creation
    pub fn new(vcx: &'vir vir::VirCtxt<'tcx>, base_name: &str, snap_inst: vir::Type<'vir>) -> Self {
        let ref_to_pred = vir::PredicateIdent::new(
            vir::vir_format!(vcx, "p_{base_name}"),
            vir::UnaryArity::new(&[&vir::TypeData::Ref]),
        );
        let ref_to_snap = FunctionIdent::new(
            vir::vir_format!(vcx, "{}_snap", ref_to_pred.name()),
            UnaryArity::new(vcx.alloc_array(&[&vir::TypeData::Ref])),
            snap_inst
        );
        let unreachable_to_snap = FunctionIdent::new(
            vir::vir_format!(vcx, "{}_unreachable", ref_to_pred.name()),
            NullaryArity::new(vcx.alloc_array(&[])),
            snap_inst
        );
        let method_assign = MethodIdent::new(
            vir::vir_format!(vcx, "assign_{}", ref_to_pred.name()),
            BinaryArity::new(vcx.alloc_array(&[&vir::TypeData::Ref, snap_inst])),
        );
        let self_ex = vcx.mk_local_ex("self", &vir::TypeData::Ref);
        let self_pred_read = ref_to_pred.apply(vcx, [self_ex], Some(vcx.mk_wildcard()));
        let self_decl = vcx.alloc_array(&[vcx.mk_local_decl("self", &vir::TypeData::Ref)]);
        Self { vcx, snap_inst, ref_to_pred, ref_to_snap, unreachable_to_snap, method_assign, self_ex, self_pred_read, self_decl, fields: Vec::new(), predicates: Vec::new(), ref_to_field_refs: Vec::new() }
    }
    pub fn tcx(&self) -> ty::TyCtxt<'tcx> {
        self.vcx.tcx
    }

    // Ref creation
    pub fn mk_struct_ref(&mut self, base_name: Option<&str>, snap_data: DomainDataStruct<'vir>) -> PredicateEncDataStruct<'vir> {
        let mut post = None;
        let ref_to_field_refs: Vec<_> = (0..snap_data.field_access.len()).map(|idx| {
            let posts = post.unwrap_or_else(|| {
                // result is null iff input is null (will be null if reference
                // created in pure code).
                let in_null = self.vcx.mk_eq_expr(self.self_ex, self.vcx.mk_null());
                let out_null = self.vcx.mk_eq_expr(self.vcx.mk_result(&vir::TypeData::Ref), self.vcx.mk_null());
                self.vcx.alloc_slice(&[self.vcx.mk_eq_expr(in_null, out_null)])
            });
            post = Some(posts);
            let name = vir::vir_format!(self.vcx, "{}_field_{idx}", base_name.unwrap_or(self.ref_to_pred.name()));
            let field = self.vcx.mk_function(name, self.self_decl, &vir::TypeData::Ref, &[], posts, None);
            self.ref_to_field_refs.push(field);
            FunctionIdent::new(name, UnaryArity::new(&[&vir::TypeData::Ref]), &vir::TypeData::Ref)
        }).collect();
        PredicateEncDataStruct {
            snap_data,
            ref_to_field_refs: self.vcx.alloc_slice(&ref_to_field_refs),
        }
    }
    pub fn mk_ref_ref(&mut self, snap_data: DomainDataStruct<'vir>, mutbl: bool) -> PredicateEncDataRef<'vir> {
        let name = vir::vir_format!(self.vcx, "{}_ref", self.ref_to_pred.name());
        let ref_field = self.vcx.mk_field(name, &vir::TypeData::Ref);
        self.fields.push(ref_field);
        let perm = if mutbl {
            None
        } else {
            Some(self.vcx.mk_wildcard())
        };
        PredicateEncDataRef { ref_field, perm, snap_data }
    }
    pub fn mk_enum_ref(&mut self, snap_data: Option<DomainDataEnum<'vir>>) -> Option<PredicateEncDataEnum<'vir>> {
        snap_data.map(|data| {
            let name = vir::vir_format!(self.vcx, "{}_discr", self.ref_to_pred.name());
            let discr = self.vcx.mk_field(name, data.discr_ty);
            self.fields.push(discr);
            let variants: Vec<_> = data.variants.iter().map(|variant| {
                let base_name = vir::vir_format!(self.vcx, "{}_{}", self.ref_to_pred.name(), variant.name);
                let predicate = vir::PredicateIdent::new(base_name, vir::UnaryArity::new(&[&vir::TypeData::Ref]));
                let fields = self.mk_struct_ref(Some(base_name), variant.fields);
                PredicateEncDataVariant {
                    predicate,
                    vid: variant.vid,
                    discr: variant.discr,
                    fields,
                }
            }).collect();
            PredicateEncDataEnum { discr, discr_prim: data.discr_prim, discr_bounds: data.discr_bounds, snap_to_discr_snap: data.snap_to_discr_snap, variants: self.vcx.alloc_slice(&variants) }
        })
    }

    pub fn output_ref(&self, specifics: PredicateEncData<'vir>) -> PredicateEncOutputRef<'vir> {
        PredicateEncOutputRef {
            ref_to_pred: self.ref_to_pred,
            ref_to_snap: self.ref_to_snap,
            unreachable_to_snap: self.unreachable_to_snap,
            method_assign: self.method_assign,
            snapshot: self.snap_inst,
            specifics,
        }
    }

    // Intermediate values
    pub fn mk_field_apps(&self, field_fns: &[FunctionIdent<'vir, UnaryArity<'vir>>], fields: Vec<PredicateEncOutputRef<'vir>>) -> Vec<FieldApp<'vir>> {
        fields.into_iter().enumerate().map(|(idx, f)| {
            let self_field = field_fns[idx].apply(self.vcx, [self.self_ex]);
            FieldApp {
                self_field_pred: self.vcx.mk_predicate_app_expr(f.ref_to_pred.apply(self.vcx, [self_field], None)),
                self_field_snap: f.ref_to_snap.apply(self.vcx, [self_field]),
            }
        }).collect()
    }
    pub fn mk_struct_ref_to_snap_body(&mut self, predicate: Option<PredicateIdent<'vir, UnaryArity<'vir>>>, fields: Vec<FieldApp<'vir>>, field_snaps_to_snap: FunctionIdent<'vir, UnknownArity<'vir>>) -> vir::Expr<'vir> {
        let fields_pred: Vec<_> = fields.iter().map(|f| f.self_field_pred).collect();
        let expr = self.vcx.mk_conj(&fields_pred);
        self.predicates.push(self.vcx.mk_predicate(predicate.unwrap_or(self.ref_to_pred).name(), self.self_decl, Some(expr)));

        let args: Vec<_> = fields.iter().map(|f| f.self_field_snap).collect();
        let expr = field_snaps_to_snap.apply(self.vcx, &args);
        let self_pred = predicate.map(|p| p.apply(self.vcx, [self.self_ex], Some(self.vcx.mk_wildcard())));
        self.vcx.mk_unfolding_expr(self_pred.unwrap_or(self.self_pred_read), expr)
    }

    // Final results
    pub fn mk_prim(mut self, base_name: &str) -> PredicateEncOutput<'vir> {
        let name = vir::vir_format!(self.vcx, "f_{base_name}");
        let field = self.vcx.mk_field(name, self.snap_inst);
        self.fields.push(field);

        let self_field_acc = self.vcx.mk_acc_field_expr(self.self_ex, field, None);
        self.predicates.push(self.vcx.mk_predicate(self.ref_to_pred.name(), self.self_decl, Some(self_field_acc)));

        let self_field = self.vcx.mk_field_expr(self.self_ex, field);
        let fn_snap_body = self.vcx.mk_unfolding_expr(self.self_pred_read, self_field);
        self.finalize(Some(fn_snap_body))
    }
    pub fn mk_param(mut self) -> PredicateEncOutput<'vir> {
        self.predicates.push(self.vcx.mk_predicate(self.ref_to_pred.name(), self.self_decl, None));
        self.finalize(None)
    }
    pub fn mk_struct(self, fn_snap_body: vir::Expr<'vir>) -> PredicateEncOutput<'vir> {
        self.finalize(Some(fn_snap_body))
    }
    pub fn mk_ref(mut self, inner: PredicateEncOutputRef<'vir>, data: PredicateEncDataRef<'vir>) -> PredicateEncOutput<'vir> {
        let self_field = self.vcx.mk_acc_field_expr(self.self_ex, data.ref_field, None);

        let self_ref = self.vcx.mk_field_expr(self.self_ex, data.ref_field);
        let non_null = self.vcx.mk_bin_op_expr(vir::BinOpKind::CmpNe, self_ref, self.vcx.mk_null());
        let inner_pred = self.vcx.mk_predicate_app_expr(inner.ref_to_pred.apply(self.vcx, [self_ref], data.perm));
        let predicate = self.vcx.mk_conj(&[self_field, non_null, inner_pred]);
        self.predicates.push(self.vcx.mk_predicate(self.ref_to_pred.name(), self.self_decl, Some(predicate)));

        let inner_snap = inner.ref_to_snap.apply(self.vcx, [self_ref]);
        let snap = if data.perm.is_none() {
            // `Ref` is only part of snapshots for mutable references.
            data.snap_data.field_snaps_to_snap.apply(self.vcx, &[inner_snap, self_ref])
        } else {
            data.snap_data.field_snaps_to_snap.apply(self.vcx, &[inner_snap])
        };
        let fn_snap_body = self.vcx.mk_unfolding_expr(self.self_pred_read, snap);
        self.finalize(Some(fn_snap_body))
    }
    pub fn mk_enum(mut self, data: Option<(PredicateEncDataEnum<'vir>, Vec<(abi::VariantIdx, Vec<PredicateEncOutputRef<'vir>>)>)>) -> PredicateEncOutput<'vir> {
        let mut predicate_body = self.vcx.mk_bool::<false>();
        let fn_snap_body = data.map(|(data, fields)| {
            let discr_acc = self.vcx.mk_acc_field_expr(self.self_ex, data.discr, None);
            let discr = data.discr_prim.snap_to_prim.apply(self.vcx, [self.vcx.mk_field_expr(self.self_ex, data.discr)]);

            let mut variants: Vec<_> = data.variants.iter().zip(fields).map(|(variant, (vid, fields))| {
                let field_fns = variant.fields.ref_to_field_refs;
                assert_eq!(variant.vid, vid);
                let fields = self.mk_field_apps(field_fns, fields);
                let body = self.mk_struct_ref_to_snap_body(Some(variant.predicate), fields, variant.fields.snap_data.field_snaps_to_snap);
                let cond = self.vcx.mk_eq_expr(discr, variant.discr);
                let pred = self.vcx.mk_predicate_app_expr(variant.predicate.apply(self.vcx, [self.self_ex], None));
                (cond, pred, body)
            }).collect();
            predicate_body = variants.iter().fold(predicate_body, |acc, (cond, pred, _)| self.vcx.mk_ternary_expr(cond, pred, acc));

            let bounds = match data.discr_bounds {
                DiscrBounds::Range { lower, upper } => {
                    let lower = self.vcx.mk_bin_op_expr(vir::BinOpKind::CmpLe, lower, discr);
                    let upper = self.vcx.mk_bin_op_expr(vir::BinOpKind::CmpLe, discr, upper);
                    self.vcx.mk_bin_op_expr(vir::BinOpKind::And, lower, upper)
                }
                DiscrBounds::Explicit(values) => {
                    let values: Vec<_> = values.iter().map(|v| self.vcx.mk_eq_expr(discr, v)).collect();
                    self.vcx.mk_disj(&values)
                }
            };
            predicate_body = self.vcx.mk_conj(&[discr_acc, bounds, predicate_body]);

            let (_, _, body) = variants.pop().unwrap();
            let body = variants.into_iter().fold(body, |acc, (cond, _, body)| self.vcx.mk_ternary_expr(cond, body, acc));
            self.vcx.mk_unfolding_expr(self.self_pred_read, body)
        });
        self.predicates.push(self.vcx.mk_predicate(self.ref_to_pred.name(), self.self_decl, Some(predicate_body)));
        self.finalize(fn_snap_body)
    }

    fn finalize(self, fn_snap_body: Option<vir::Expr<'vir>>) -> PredicateEncOutput<'vir> {
        let function_snap = self.vcx.mk_function(
            self.ref_to_snap.name(),
            self.self_decl,
            self.snap_inst,
            self.vcx.alloc_slice(&[self.vcx.mk_predicate_app_expr(self.self_pred_read)]),
            &[],
            fn_snap_body
        );
        // unreachable_to_snap
        let name = self.unreachable_to_snap.name();
        let false_ = self.vcx.alloc_slice(&[self.vcx.mk_bool::<false>()]);
        let unreachable_to_snap = self.vcx.mk_function(name, &[], self.snap_inst, false_, false_, None);

        // method_assign
        let name = self.method_assign.name();
        let self_new_local = self.vcx.mk_local("self_new", self.snap_inst);
        let args = self.vcx.alloc_slice(&[
            self.self_decl[0],
            self.vcx.mk_local_decl_local(self_new_local),
        ]);
        let posts = self.vcx.alloc_slice(&[
            self.vcx.mk_predicate_app_expr(self.ref_to_pred.apply(self.vcx, [self.self_ex], None)),
            self.vcx.mk_eq_expr(
                self.ref_to_snap.apply(self.vcx, [self.self_ex]),
                self.vcx.mk_local_ex_local(self_new_local)
            ),
        ]);
        let method_assign = self.vcx.mk_method(name, args, &[], &[], posts, None);
        PredicateEncOutput {
            fields: self.fields,
            predicates: self.predicates,
            function_snap,
            unreachable_to_snap,
            ref_to_field_refs: self.ref_to_field_refs,
            method_assign,
        }
    }
}

struct FieldApp<'vir> {
    self_field_pred: vir::Expr<'vir>,
    self_field_snap: vir::Expr<'vir>,
}
