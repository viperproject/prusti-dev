use prusti_rustc_interface::{
    middle::ty::{self, TyKind, util::IntTypeExt, IntTy, UintTy},
    abi,
    span::symbol,
};
use task_encoder::{
    TaskEncoder,
    TaskEncoderDependencies,
};
use vir::{BinaryArity, UnaryArity, UnknownArity, FunctionIdent, CallableIdent, Arity, ToKnownArity, Function};

/// You probably never want to use this, use `SnapshotEnc` instead.
/// Note: there should never be a dependency on `PredicateEnc` inside this
/// encoder!
pub(super) struct DomainEnc;

#[derive(Clone, Copy, Debug)]
pub struct FieldFunctions<'vir> {
    /// Snapshot of self as argument. Returns domain of field.
    pub read: FunctionIdent<'vir, UnaryArity<'vir>>,
    /// Snapshot of self as first argument and of field as second. Returns
    /// updated domain of self.
    pub write: FunctionIdent<'vir, BinaryArity<'vir>>,
}

#[derive(Clone, Copy, Debug)]
pub struct DomainDataPrim<'vir> {
    pub prim_type: vir::Type<'vir>,
    /// Snapshot of self as argument. Returns Viper primitive value.
    pub snap_to_prim: FunctionIdent<'vir, UnaryArity<'vir>>,
    /// Viper primitive value as argument. Returns domain.
    pub prim_to_snap: FunctionIdent<'vir, UnaryArity<'vir>>,
}
#[derive(Clone, Copy, Debug)]
pub struct DomainDataStruct<'vir> {
    /// Construct domain from snapshots of fields or for primitive types
    /// from the single Viper primitive value. `None` for generic parameters.
    pub field_snaps_to_snap: FunctionIdent<'vir, UnknownArity<'vir>>,
    /// Functions to access the fields.
    pub field_access: &'vir [FieldFunctions<'vir>],
}
#[derive(Clone, Copy, Debug)]
pub struct DomainDataEnum<'vir> {
    pub discr_ty: vir::Type<'vir>,
    pub discr_prim: DomainDataPrim<'vir>,
    pub discr_bounds: DiscrBounds<'vir>,
    pub snap_to_discr_snap: FunctionIdent<'vir, UnaryArity<'vir>>,
    pub variants: &'vir [DomainDataVariant<'vir>],
}
#[derive(Clone, Copy, Debug)]
pub struct DomainDataVariant<'vir> {
    pub name: symbol::Symbol,
    pub vid: abi::VariantIdx,
    pub discr: vir::Expr<'vir>,
    pub fields: DomainDataStruct<'vir>,
}

#[derive(Clone, Copy, Debug)]
pub enum DiscrBounds<'vir> {
    Range { lower: vir::Expr<'vir>, upper: vir::Expr<'vir> },
    Explicit(&'vir [vir::Expr<'vir>]),
}

#[derive(Clone, Copy, Debug)]
pub enum DomainEncSpecifics<'vir> {
    Param,
    Primitive(DomainDataPrim<'vir>),
    // structs, tuples
    StructLike(DomainDataStruct<'vir>),
    EnumLike(Option<DomainDataEnum<'vir>>)
}

#[derive(Clone, Debug)]
pub struct DomainEncOutputRef<'vir> {
    pub base_name: String,
    pub domain: vir::DomainIdentUnknownArity<'vir>,
}
impl<'vir> task_encoder::OutputRefAny for DomainEncOutputRef<'vir> {}

use crate::encoders::SnapshotEnc;

pub fn all_outputs<'vir>() -> Vec<vir::Domain<'vir>> {
    DomainEnc::all_outputs()
}

impl TaskEncoder for DomainEnc {
    task_encoder::encoder_cache!(DomainEnc);

    type TaskDescription<'vir> = ty::Ty<'vir>;

    type OutputRef<'vir> = DomainEncOutputRef<'vir>;
    type OutputFullDependency<'vir> = DomainEncSpecifics<'vir>;
    type OutputFullLocal<'vir> = vir::Domain<'vir>;
    //type OutputFullDependency<'vir> = DomainEncOutputDep<'vir>;

    type EncodingError = ();

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
        vir::with_vcx(|vcx| match task_key.kind() {
            TyKind::Bool | TyKind::Char | TyKind::Int(_) | TyKind::Uint(_) | TyKind::Float(_)  => {
                let (base_name, prim_type) = match task_key.kind() {
                    TyKind::Bool => (String::from("Bool"), &vir::TypeData::Bool),
                    TyKind::Int(kind) => (
                        format!("Int_{}", kind.name_str()),
                        &vir::TypeData::Int,
                    ),
                    TyKind::Uint(kind) => (
                        format!("Uint_{}", kind.name_str()),
                        &vir::TypeData::Int,
                    ),
                    _ => todo!(),
                };

                let (mut enc, _) = DomainEncData::new(vcx, &base_name, [].into_iter());
                deps.emit_output_ref::<Self>(*task_key, enc.output_ref(base_name));
                let specifics = enc.mk_prim_specifics(*task_key, prim_type);
                Ok((enc.finalize(), specifics))
            }
            TyKind::Param(param) => {
                let base_name = param.name.as_str().to_string();
                let (enc, _) = DomainEncData::new(vcx, &base_name, [].into_iter());
                deps.emit_output_ref::<Self>(*task_key, enc.output_ref(base_name));
                Ok((enc.finalize(), DomainEncSpecifics::Param))
            }
            TyKind::Adt(adt, params) => {
                let base_name = vcx.tcx().item_name(adt.did()).to_ident_string();
                let ty_params = params.iter().flat_map(ty::GenericArg::as_type);
                let (mut enc, ty_params) = DomainEncData::new(vcx, &base_name, ty_params);
                deps.emit_output_ref::<Self>(*task_key, enc.output_ref(base_name));
                match adt.adt_kind() {
                    ty::AdtKind::Struct => {
                        let fields = if !adt.is_box() {
                            let variant = adt.non_enum_variant();
                            enc.mk_field_tys(deps, variant, &ty_params, params)
                        } else {
                            // Box special case (this should be replaced by an
                            // extern spec in the future)
                            let TyKind::Param(param) = params[0].expect_ty().kind() else {
                                unreachable!("Box with non-param type");
                            };
                            vec![ty_params[SnapshotEnc::from_viper_param(param.index) as usize]]
                        };
                        let specifics = enc.mk_struct_specifics(fields);
                        Ok((enc.finalize(), specifics))
                    }
                    ty::AdtKind::Enum => {
                        let variants: Vec<_> = adt.discriminants(vcx.tcx()).map(|(v, d)| {
                            let variant = adt.variant(v);
                            let field_tys = enc.mk_field_tys(deps, variant, &ty_params, params);
                            (variant.name, v, field_tys, d)
                        }).collect();
                        let variants = if variants.is_empty() {
                            None
                        } else {
                            let has_explicit = adt.variants().iter().any(|v| matches!(v.discr, ty::VariantDiscr::Explicit(_)));
                            let discr_ty = adt.repr().discr_type().to_ty(vcx.tcx());
                            let discr_ty = deps.require_local::<SnapshotEnc>(discr_ty).unwrap();
                            Some(VariantData {
                                discr_ty: discr_ty.snapshot,
                                discr_prim: discr_ty.specifics.expect_primitive(),
                                has_explicit,
                                variants,
                            })
                        };
                        let specifics = enc.mk_enum_specifics(variants);
                        Ok((enc.finalize(), specifics))
                    }
                    ty::AdtKind::Union => todo!(),
                }
            }
            TyKind::Tuple(params) => {
                let base_name = format!("{}_Tuple", params.len());
                let (mut enc, ty_params) = DomainEncData::new(vcx, &base_name, params.iter());
                deps.emit_output_ref::<Self>(*task_key, enc.output_ref(base_name));
                let specifics = enc.mk_struct_specifics(ty_params);
                Ok((enc.finalize(), specifics))
            }
            TyKind::Never => {
                let base_name = String::from("Never");
                let (mut enc, _) = DomainEncData::new(vcx, &base_name, [].into_iter());
                deps.emit_output_ref::<Self>(*task_key, enc.output_ref(base_name));
                let specifics = enc.mk_enum_specifics(None);
                Ok((enc.finalize(), specifics))
            }
            &TyKind::Ref(_, inner, m) => {
                let base_name = format!("Ref_{m:?}");
                let (mut enc, mut ty_params) = DomainEncData::new(vcx, &base_name, [inner].into_iter());
                deps.emit_output_ref::<Self>(*task_key, enc.output_ref(base_name));
                if m.is_mut() {
                    ty_params.push(&vir::TypeData::Ref);
                }
                let specifics = enc.mk_struct_specifics(ty_params);
                Ok((enc.finalize(), specifics))
            }
            kind => todo!("{kind:?}"),
        })
    }
}

impl DomainEnc {
    fn get_bit_width(tcx: ty::TyCtxt, ty: ty::Ty) -> u64 {
        let pointer_size = tcx.data_layout.pointer_size.bits() as u32;
        match ty.kind() {
            // TODO: maybe we don't want to use the target architecture bit-width when verifying?
            ty::TyKind::Int(ty) => ty.normalize(pointer_size).bit_width().unwrap(),
            ty::TyKind::Uint(ty) => ty.normalize(pointer_size).bit_width().unwrap(),
            kind => unreachable!("tried to get bit width of non-integer type {kind:?}"),
        }
    }
}

impl DomainEnc {
    pub fn expect_param(ty: ty::Ty) -> ty::ParamTy {
        match ty.kind() {
            TyKind::Param(param) => *param,
            _ => panic!("non-param ty: {ty}"),
        }
    }
}

pub struct VariantData<'vir, 'tcx>  {
    discr_ty: vir::Type<'vir>,
    discr_prim: DomainDataPrim<'vir>,
    /// Do any of the variants have an explicit discriminant value?
    has_explicit: bool,
    variants: Vec<(symbol::Symbol, abi::VariantIdx, Vec<vir::Type<'vir>>, ty::util::Discr<'tcx>)>,
}

struct DomainEncData<'vir, 'tcx> {
    vcx: &'vir vir::VirCtxt<'tcx>,
    domain: vir::DomainIdentUnknownArity<'vir>,
    self_ty: vir::Type<'vir>,
    self_ex: vir::Expr<'vir>,
    self_decl: &'vir [vir::LocalDecl<'vir>; 1],
    axioms: Vec<vir::DomainAxiom<'vir>>,
    functions: Vec<vir::DomainFunction<'vir>>,
}
impl<'vir, 'tcx> DomainEncData<'vir, 'tcx> {
    // Creation
    pub fn new(vcx: &'vir vir::VirCtxt<'tcx>, base_name: &str, params: impl Iterator<Item = ty::Ty<'tcx>>) -> (Self, Vec<vir::Type<'vir>>) {
        let domain_params: Vec<_> = params
            // The `task_to_key` translation should ensure that only `Param`s are allowed here.
            .map(DomainEnc::expect_param)
            .map(|param| vcx.alloc(vir::DomainParamData {
                name: vir::vir_format!(vcx, "{}", param.name.as_str()),
            })).collect();
        let domain = vir::DomainIdentUnknownArity::new(
            vir::vir_format!(vcx, "s_{base_name}"),
            vir::UnknownArityAny::new(vcx.alloc_slice(&domain_params))
        );
        let ty_params: Vec<_> = domain_params.into_iter().map(|t| vcx.alloc(vir::TypeData::DomainTypeParam(*t))).collect();
        let self_ty = domain.apply(vcx, &ty_params);
        let self_local = vcx.mk_local("self", self_ty);
        let self_ex = vcx.mk_local_ex_local(self_local);
        let self_decl = vcx.alloc_array(&[vcx.mk_local_decl_local(self_local)]);
        (Self { vcx, domain, self_ty, self_ex, self_decl, axioms: Vec::new(), functions: Vec::new() }, ty_params)
    }

    // Intermediate values
    pub fn mk_field_tys(
        &self,
        deps: &mut TaskEncoderDependencies<'vir>,
        variant: &ty::VariantDef,
        ty_params: &Vec<vir::Type<'vir>>,
        params: ty::GenericArgsRef<'tcx>,
    ) -> Vec<vir::Type<'vir>> {
        variant.fields.iter().map(|f| f.ty(self.vcx.tcx(), params)).map(|ty| match *ty.kind() {
            TyKind::Param(param) => ty_params[SnapshotEnc::from_viper_param(param.index) as usize],
            _ => deps.require_ref::<SnapshotEnc>(ty).unwrap().snapshot,
        }).collect()
    }

    // Creating specifics
    pub fn mk_prim_specifics(
        &mut self,
        ty: ty::Ty<'tcx>,
        prim_type: vir::Type<'vir>,
    ) -> DomainEncSpecifics<'vir> {
        let prim_type_args = self.vcx.alloc_array(&[prim_type]);
        let data = self.mk_field_functions(prim_type_args, None, ty.is_integral());
        // TODO: what to do about write?
        let snap_to_prim = data.field_access[0].read;
        let specifics = DomainDataPrim {
            prim_type,
            snap_to_prim,
            prim_to_snap: data.field_snaps_to_snap.to_known(),
        };
        specifics.bounds(ty).map(|(lower, upper)| {
            let exp = snap_to_prim.apply(self.vcx, [self.self_ex]);
            let axiom = self.mk_bounds_axiom(self.domain.name(), exp, lower, upper);
            self.axioms.push(axiom);
        });
        DomainEncSpecifics::Primitive(specifics)
    }
    pub fn mk_struct_specifics(
        &mut self,
        fields: Vec<vir::Type<'vir>>,
    ) -> DomainEncSpecifics<'vir> {
        let specifics = self.mk_field_functions(self.vcx.alloc_slice(&fields), None, false);
        DomainEncSpecifics::StructLike(specifics)
    }
    pub fn mk_enum_specifics(
        &mut self,
        data: Option<VariantData<'vir, 'tcx>>,
    ) -> DomainEncSpecifics<'vir> {
        let specifics = data.map(|data| {
            let discr_vals: Vec<_> = data.variants.iter().map(|(_, _, _, discr)| data.discr_prim.expr_from_bits(discr.ty, discr.val)).collect();
            let snap_to_discr_snap = self.mk_discr_function(data.discr_ty);
            let variants = self.vcx.alloc_slice(&data.variants.iter().enumerate().map(|(idx, (name, vid, fields, _))| {
                let discr = (snap_to_discr_snap, data.discr_prim.prim_to_snap.apply(self.vcx, [discr_vals[idx]]), *name);
                let fields = self.mk_field_functions(self.vcx.alloc_slice(fields), Some(discr), false);
                DomainDataVariant { name: *name, vid: *vid, discr: discr_vals[idx], fields }
            }).collect::<Vec<_>>());
            let discr_bounds = self.mk_discr_bounds_axioms(data.discr_prim, snap_to_discr_snap, discr_vals, data.has_explicit);
            DomainDataEnum {
                discr_ty: data.discr_ty,
                discr_prim: data.discr_prim,
                discr_bounds,
                snap_to_discr_snap,
                variants,
            }
        });
        DomainEncSpecifics::EnumLike(specifics)
    }

    fn push_function(&mut self, func: vir::DomainFunction<'vir>) -> FunctionIdent<'vir, UnknownArity<'vir>> {
        let ident = func.ident();
        self.functions.push(func);
        ident
    }

    // Helper functions
    fn mk_field_functions(
        &mut self,
        field_tys: &'vir [vir::Type<'vir>],
        discr: Option<(FunctionIdent<'vir, UnaryArity<'vir>>, vir::Expr<'vir>, symbol::Symbol)>,
        stronger_cons_axiom: bool,
    ) -> DomainDataStruct<'vir> {
        let name = self.domain.name();
        let base = discr.map(|(_, _, v)| format!("{name}_{v}")).unwrap_or_else(|| name.to_string());
        // Constructor
        let field_snaps_to_snap = {
            let name = vir::vir_format!(self.vcx, "{base}_cons");
            self.push_function(self.vcx.mk_domain_function(false, name, field_tys, self.self_ty))
        };

        // Variables and definitions useful for axioms
        let fnames = field_tys.iter().enumerate().map(|(idx, ty)|
            self.vcx.mk_local(vir::vir_format!(self.vcx, "f{idx}"), ty)
        ).collect::<Vec<_>>();
        let cons_qvars: Vec<_> = field_tys.iter().enumerate().map(|(idx, ty)|
            self.vcx.mk_local_decl_local(fnames[idx])
        ).collect();
        let cons_qvars = self.vcx.alloc_slice(&cons_qvars);
        let cons_args: Vec<_> = fnames.into_iter().map(|fname| self.vcx.mk_local_ex_local(fname)).collect();
        let cons_call_with_qvars = field_snaps_to_snap.apply(self.vcx, &cons_args);

        // Discriminant axioms
        if let Some((get_discr, val, _)) = discr {
            let discr = get_discr.apply(self.vcx, [cons_call_with_qvars]);
            let mut expr = self.vcx.mk_bin_op_expr(vir::BinOpKind::CmpEq, discr, val);
            if !field_tys.is_empty() {
                expr = self.vcx.mk_forall_expr(
                    cons_qvars,
                    self.vcx.alloc_slice(&[self.vcx.mk_trigger(&[discr])]),
                    expr,
                );
            }
            self.axioms.push(self.vcx.mk_domain_axiom(
                vir::vir_format!(self.vcx, "ax_{base}_cons_discr"),
                expr,
            ));
        }

        // Accessors
        let field_access = {
            field_tys.iter().enumerate().map(|(idx, field_ty)| {
                // Read
                let name = vir::vir_format!(self.vcx, "{base}_read_{idx}");
                let args = self.vcx.alloc_array(&[self.self_ty]);
                let read = FunctionIdent::new(
                    name,
                    UnaryArity::new(args),
                    field_ty
                );
                self.functions.push(self.vcx.mk_domain_function(false, name, args, field_ty));

                let cons_read = read.apply(self.vcx, [cons_call_with_qvars]);
                self.axioms.push(self.vcx.mk_domain_axiom(
                    vir::vir_format!(self.vcx, "ax_{base}_cons_read_{idx}"),
                    self.vcx.mk_forall_expr(
                        cons_qvars,
                        self.vcx.alloc_slice(&[self.vcx.mk_trigger(&[cons_call_with_qvars])]),
                        self.vcx.mk_bin_op_expr(vir::BinOpKind::CmpEq, cons_read, cons_args[idx])
                    )
                ));

                // Write
                let name = vir::vir_format!(self.vcx, "{base}_write_{idx}");
                let args = self.vcx.alloc_array(&[self.self_ty, field_ty]);
                let write = FunctionIdent::new(
                    name,
                    BinaryArity::new(args),
                    self.self_ty
                );
                self.functions.push(self.vcx.mk_domain_function(false, name, args, self.self_ty));
                FieldFunctions { read, write }
            }).collect::<Vec<_>>()
        };

        { // Other axioms
            // TODO: this axiom seems useful even when there are no fields, but
            // I can't figure out which triggers it would have. Is it ok to skip
            // it?
            if !field_access.is_empty() {
                // Constructing from reads leads to same result
                let all_reads: Vec<_> = field_access.iter().map(|field_access| field_access.read.apply(self.vcx, [self.self_ex])).collect();
                let cons_call_with_reads = field_snaps_to_snap.apply(self.vcx, &all_reads);
                let trigger = if stronger_cons_axiom {
                    // Integer types require a simpler trigger to be complete
                    // when snapshot equality may be used on them.
                    assert_eq!(all_reads.len(), 1);
                    all_reads[0]
                } else {
                    cons_call_with_reads
                };
                self.axioms.push(self.vcx.mk_domain_axiom(
                    vir::vir_format!(self.vcx, "ax_{base}_cons"),
                    self.vcx.mk_forall_expr(
                        self.self_decl,
                        self.vcx.alloc_slice(&[self.vcx.mk_trigger(&[trigger])]),
                        self.vcx.mk_bin_op_expr(vir::BinOpKind::CmpEq, cons_call_with_reads, self.self_ex)
                    )
                ));
            };

            // Write and read to different fields change nothing, write and read to
            // the same field sees the new value.
            for (wi, write) in field_access.iter().enumerate() {
                let val_local = self.vcx.mk_local("val", field_tys[wi]);
                let val = self.vcx.mk_local_ex_local(val_local);
                let decl = self.vcx.mk_local_decl_local(val_local);
                let write = write.write.apply(self.vcx, [self.self_ex, val]);
                for (ri, read) in field_access.iter().enumerate() {
                    let write_read = read.read.apply(self.vcx, [write]);
                    let rhs = if wi == ri { val } else { read.read.apply(self.vcx, [self.self_ex]) };
                    self.axioms.push(
                        self.vcx.mk_domain_axiom(
                            vir::vir_format!(self.vcx, "ax_{base}_write_{wi}_read_{ri}"),
                            self.vcx.mk_forall_expr(
                                self.vcx.alloc_slice(&[self.self_decl[0], decl]),
                                self.vcx.alloc_slice(&[self.vcx.mk_trigger(&[write_read])]),
                                self.vcx.mk_bin_op_expr(vir::BinOpKind::CmpEq, write_read, rhs)
                            )
                        )
                    );
                }
            }
        }

        DomainDataStruct { field_snaps_to_snap, field_access: self.vcx.alloc_slice(&field_access) }
    }
    fn mk_discr_function(
        &mut self,
        discr_ty: vir::Type<'vir>,
    ) -> FunctionIdent<'vir, UnaryArity<'vir>> {
        let name = vir::vir_format!(self.vcx, "{}_discr", self.domain.name());
        let types = self.vcx.alloc_array(&[self.self_ty]);
        let snap_to_discr_snap = FunctionIdent::new(
            name,
            UnaryArity::new(types),
            discr_ty
        );
        self.functions.push(self.vcx.mk_domain_function(false, name, types, discr_ty));
        snap_to_discr_snap
    }
    fn mk_discr_bounds_axioms(
        &mut self,
        discr_prim: DomainDataPrim<'vir>,
        snap_to_discr_snap: FunctionIdent<'vir, UnaryArity<'vir>>,
        discr_vals: Vec<vir::Expr<'vir>>,
        has_explicit: bool,
    ) -> DiscrBounds<'vir> {
        let discr = snap_to_discr_snap.apply(self.vcx, [self.self_ex]);
        let discr_prim = discr_prim.snap_to_prim.apply(self.vcx, [discr]);
        if has_explicit {
            let discr_vals_eq: Vec<_> = discr_vals.iter().map(|val| self.vcx.mk_eq_expr(discr_prim, *val)).collect();
            let body = self.vcx.mk_disj(&discr_vals_eq);
            self.axioms.push(self.vcx.mk_domain_axiom(
                vir::vir_format!(self.vcx, "{}_discr_values", self.domain.name()),
                self.vcx.mk_forall_expr(
                    self.self_decl,
                    // TODO: should we use `discr` instead of `discr_prim` here?
                    self.vcx.alloc_slice(&[self.vcx.mk_trigger(&[discr_prim])]),
                    body
                )
            ));
            DiscrBounds::Explicit(self.vcx.alloc_slice(&discr_vals))
        } else {
            let base = format!("{}_discr", self.domain.name());
            let lower = discr_vals.first().unwrap();
            let upper = discr_vals.last().unwrap();
            let axiom = self.mk_bounds_axiom(&base, discr_prim, lower, upper);
            self.axioms.push(axiom);
            DiscrBounds::Range { lower, upper }
        }
    }
    fn mk_bounds_axiom(
        &self,
        base: &str,
        exp: vir::Expr<'vir>,
        lower: vir::Expr<'vir>,
        upper: vir::Expr<'vir>,
    ) -> vir::DomainAxiom<'vir> {
        let lower = self.vcx.mk_bin_op_expr(vir::BinOpKind::CmpLe, lower, exp);
        let upper = self.vcx.mk_bin_op_expr(vir::BinOpKind::CmpLe, exp, upper);
        self.vcx.mk_domain_axiom(vir::vir_format!(self.vcx, "{base}_bounds"), self.vcx.mk_forall_expr(
            self.self_decl,
            self.vcx.alloc_slice(&[self.vcx.mk_trigger(&[exp])]),
            self.vcx.mk_bin_op_expr(vir::BinOpKind::And, lower, upper)
        ))
    }

    // Final results
    fn output_ref(&self, base_name: String) -> DomainEncOutputRef<'vir> {
        DomainEncOutputRef {
            base_name,
            domain: self.domain,
        }
    }
    fn finalize(self) -> vir::Domain<'vir> {
        self.vcx.mk_domain(
            self.domain.name(),
            self.domain.arity().args(),
            self.vcx.alloc_slice(&self.axioms),
            self.vcx.alloc_slice(&self.functions),
        )
    }
}

// Utility functions

impl<'vir> DomainEncSpecifics<'vir> {
    pub fn expect_primitive(self) -> DomainDataPrim<'vir> {
        match self {
            Self::Primitive(data) => data,
            _ => panic!("expected primitive"),
        }
    }
    pub fn expect_structlike(self) -> DomainDataStruct<'vir> {
        match self {
            Self::StructLike(data) => data,
            _ => panic!("expected struct-like"),
        }
    }
    pub fn get_enumlike(self) -> Option<Option<DomainDataEnum<'vir>>> {
        match self {
            Self::EnumLike(data) => Some(data),
            _ => None,
        }
    }
    pub fn expect_enumlike(self) -> Option<DomainDataEnum<'vir>> {
        self.get_enumlike().expect("expected enum-like")
    }
}
impl<'vir> DomainDataPrim<'vir> {
    pub fn expr_from_bits<'tcx>(&self, ty: ty::Ty<'tcx>, value: u128) -> vir::Expr<'vir> {
        match *self.prim_type {
            vir::TypeData::Bool => vir::with_vcx(|vcx| vcx.mk_const_expr(vir::ConstData::Bool(value != 0))),
            vir::TypeData::Int => {
                let (bit_width, signed) = match ty.kind() {
                    TyKind::Int(IntTy::Isize) => ((std::mem::size_of::<isize>() * 8) as u64, true),
                    TyKind::Int(ty) => (ty.bit_width().unwrap(), true),
                    TyKind::Uint(UintTy::Usize) => ((std::mem::size_of::<usize>() * 8) as u64, true),
                    TyKind::Uint(ty) => (ty.bit_width().unwrap(), false),
                    kind => unreachable!("{kind:?}"),
                };
                let size = abi::Size::from_bits(bit_width);
                let negative_value = if signed {
                    let value = size.sign_extend(value) as i128;
                    Some(value).filter(|value| value.is_negative())
                } else {
                    None
                };
                match negative_value {
                    Some(value) => vir::with_vcx(|vcx| {
                        let value = vcx.mk_const_expr(vir::ConstData::Int(value.unsigned_abs()));
                        vcx.mk_unary_op_expr(vir::UnOpKind::Neg, value)
                    }),
                    None =>
                        vir::with_vcx(|vcx| vcx.mk_const_expr(vir::ConstData::Int(value))),
                }
            },
            ref k => unreachable!("{k:?}"),
        }
    }
    fn bounds<'tcx>(&self, ty: ty::Ty<'tcx>) -> Option<(vir::Expr<'vir>, vir::Expr<'vir>)> {
        match *self.prim_type {
            vir::TypeData::Bool => None,
            ref int@vir::TypeData::Int { .. } => {
                let rust_ty = ty.kind();
                Some(vir::with_vcx(|vcx| (vcx.get_min_int(int, rust_ty), vcx.get_max_int(int, rust_ty))))
            },
            ref k => todo!("{k:?}"),
        }
    }
}
