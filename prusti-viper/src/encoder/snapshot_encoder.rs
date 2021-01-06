// © 2020, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use prusti_common::vir;
use crate::encoder::Encoder;
use rustc_middle::ty;
use prusti_common::vir::{PermAmount, EnumVariantIndex};
use log::warn;
use crate::encoder::errors::{EncodingError, EncodingResult, SpannedEncodingResult};
use std::borrow::Borrow;
use rustc_target::abi;
use rustc_middle::ty::layout::IntegerExt;
use rustc_target::abi::Integer;
use ::log::{info, debug, trace};
use crate::encoder::snapshot;

const SNAPSHOT_DOMAIN_PREFIX: &str = "Snap$";
const SNAPSHOT_CONS: &str = "cons$";
const SNAPSHOT_VARIANT: &str = "variant$";
const SNAPSHOT_GET: &str = "snap$";
pub const SNAPSHOT_EQUALS: &str = "equals$";
pub const SNAPSHOT_NOT_EQUALS: &str = "not_equals$";
const SNAPSHOT_ARG: &str = "_arg";
const SNAPSHOT_LEFT: &str = "_left";
const SNAPSHOT_RIGHT: &str = "_right";

pub struct SnapshotEncoder<'p, 'v: 'p, 'tcx: 'v> {
    encoder: &'p Encoder<'v, 'tcx>,
    ty: ty::Ty<'tcx>,
    predicate_name: String,
}

struct SnapshotAdtEncoder<'s, 'v: 's, 'tcx: 'v> {
    snapshot_encoder: &'s SnapshotEncoder<'s, 'v, 'tcx>,
    adt_def: &'s ty::AdtDef,
    subst: ty::subst::SubstsRef<'tcx>,
    predicate: vir::Predicate,
}

#[derive(Clone, Debug)]
pub struct SnapshotDomain {
    pub domain: vir::Domain,
    pub equals_func: vir::Function,
    pub equals_func_ref: vir::Function,
    pub not_equals_func: vir::Function,
    pub not_equals_func_ref: vir::Function,
}

impl SnapshotDomain {
    pub fn get_type(&self) -> vir::Type {
        vir::Type::Domain(
            self.domain.name.to_string()
        )
    }

    pub fn call_cons_func(&self, args: Vec<vir::Expr>) -> vir::Expr {
        let cons_function = self.domain.functions[0].clone();
        vir::Expr::domain_func_app(cons_function, args)
    }
    /* TODO use this once the signature of DomainFuncApp has been corrected
    pub fn call_snap_func(&self, args: Vec<vir::Expr>) -> vir::Expr {
        let cons_function = self.domain.functions[0].clone();
        vir::Expr::DomainFuncApp(
            cons_function.name,
            args,
            cons_function.formal_args,
            cons_function.return_type,
            cons_function.domain_name,
            vir::Position::default()
        )
    }
     */
}

#[derive(Clone, Debug)]
pub struct Snapshot {
    pub predicate_name: String,
    pub snap_func: Option<vir::Function>,
    pub snap_domain: Option<SnapshotDomain>, // for types with fields
}

impl Snapshot {
    pub fn is_defined(&self) -> bool {
        self.snap_func.is_some()
    }

    pub fn domain(&self) -> Option<vir::Domain> {
        match &self.snap_domain {
            Some(s) => Some(s.domain.clone()),
            None => None,
        }
    }

    pub fn functions(&self) -> Vec<vir::Function> {
        let mut res = vec![];
        if self.is_defined() {
            res.push(self.snap_func.clone().unwrap())
        }
        if let Some(s) = &self.snap_domain {
            res.push(s.equals_func.clone());
            res.push(s.equals_func_ref.clone());
            res.push(s.not_equals_func.clone());
            res.push(s.not_equals_func_ref.clone());
        }
        res
    }

    pub fn snap_name(&self) -> String {
        match &self.snap_func {
            Some(func) => func.name.to_string(),
            None => unreachable!(),
        }
    }

    pub fn get_type(&self) -> vir::Type {
        match &self.snap_func {
            Some(func) => func.return_type.clone(),
            None => unreachable!(),
        }
    }

    pub fn equals_func_name(&self) -> String {
        SNAPSHOT_EQUALS.to_string()
    }

    pub fn not_equals_func_name(&self) -> String {
        SNAPSHOT_NOT_EQUALS.to_string()
    }

    pub fn snap_call(&self, arg: vir::Expr) -> vir::Expr {
        match &self.snap_func {
            Some(func) => {
                vir::Expr::func_app(
                    self.snap_name(),
                    vec![self.dereference_expr(arg)],
                    func.formal_args.clone(),
                    self.get_type(),
                    vir::Position::default(),
                )
            }
            None => unreachable!()
        }
    }

    fn dereference_expr(&self, expr: vir::Expr) -> vir::Expr {
        match expr.try_deref() {
            Some(deref_expr) => self.dereference_expr(deref_expr),
            None => expr,
        }
    }

    pub fn encode_equals(&self, lhs: vir::Expr, rhs: vir::Expr, pos: vir::Position) -> vir::Expr {
        vir::Expr::eq_cmp(self.snap_call(lhs), self.snap_call(rhs))
    }

    pub fn encode_not_equals(&self, lhs: vir::Expr, rhs: vir::Expr, pos: vir::Position) -> vir::Expr {
        vir::Expr::ne_cmp(self.snap_call(lhs), self.snap_call(rhs))
    }
}

impl<'p, 'v, 'r: 'v, 'a: 'r, 'tcx: 'a> SnapshotEncoder<'p, 'v, 'tcx> {
    pub fn new(encoder: &'p Encoder<'v, 'tcx>, ty: ty::Ty<'tcx>, predicate_name: String) -> Self {
        SnapshotEncoder { encoder, ty, predicate_name }
    }

    pub fn encode(&self) -> EncodingResult<Snapshot> {
        if !self.is_supported() {
            return Ok(Snapshot {
                predicate_name: self.predicate_name.clone(),
                snap_func: None,
                snap_domain: None,
            })
        }

        Ok(match &self.ty.kind() {
            ty::TyKind::Int(_)
            | ty::TyKind::Uint(_)
            | ty::TyKind::Char
            | ty::TyKind::Bool => {
                self.encode_primitive(
                    self.encoder.encode_value_field(self.ty)
                )?
            }
            ty::TyKind::Param(_) => {
                self.encode_generic()?
            }
            ty::TyKind::Tuple(_) => {
                self.encode_tuple()?
            }
            ty::TyKind::Adt(adt_def, subst) if !adt_def.is_box() => {
                if adt_def.is_struct() || adt_def.is_enum() {
                    SnapshotAdtEncoder::new(
                        &self,
                        adt_def,
                        subst,
                    ).encode_snapshot()?
                } else {
                    unreachable!()
                }
            }
            x => unimplemented!("{:?}", x),
        })
    }

    fn is_supported(&self) -> bool {
        warn!("encoded {}. self.encoder.has_structural_eq_impl={:?} self.is_ty_supported(self.ty)={:?}",  self.predicate_name.clone(), self.encoder.has_structural_eq_impl(self.ty), self.is_ty_supported(self.ty));

        self.encoder.has_structural_eq_impl(self.ty)
            && self.is_ty_supported(self.ty)
    }

    fn is_ty_supported(&self, ty: ty::Ty<'tcx>) -> bool {
        match ty.kind() {
            ty::TyKind::Int(_)
            | ty::TyKind::Uint(_)
            | ty::TyKind::Char
            | ty::TyKind::Bool
            | ty::TyKind::Param(_) => {
                true
            }

            ty::TyKind::Ref(_, ref ty, _) => {
                self.is_ty_supported(ty)
            }

            ty::TyKind::Adt(adt_def, subst) if !adt_def.is_box() => {
                let tcx = self.encoder.env().tcx();
                for variant in &adt_def.variants {
                    for field in &variant.fields {
                        let field_ty = field.ty(tcx, subst);
                        if !self.is_ty_supported(field_ty) {
                            return false
                        }
                    }
                }

                true
            }
            ty::TyKind::Tuple(elems) => {
                for field_ty in *elems {
                    if !self.is_ty_supported(field_ty.expect_ty()) {
                        return false
                    }
                }
                true
            }
            _ => false
        }
    }

    fn encode_primitive(&self, field: vir::Field)
        -> EncodingResult<Snapshot>
    {
        Ok(Snapshot {
            predicate_name: self.predicate_name.clone(),
            snap_func: Some(self.encode_snap_func_primitive(field)?),
            snap_domain: None,
        })
    }

    fn encode_generic(&self) -> EncodingResult<Snapshot> {
        let snap_domain = self.encode_snap_domain()?;
        Ok(Snapshot {
            predicate_name: self.predicate_name.clone(),
            snap_func: Some(self.encode_snap_func_generic(snap_domain.get_type())),
            snap_domain: Some(snap_domain),
        })
    }

    fn encode_tuple(&self) -> EncodingResult<Snapshot> {
        let snap_domain = self.encode_snap_domain()?;
        Ok(Snapshot {
            predicate_name: self.predicate_name.clone(),
            snap_func: Some(self.encode_snap_func(
                snap_domain.get_type(),
                snap_domain.call_cons_func(
                    match self.ty.kind() {
                        ty::TyKind::Tuple(elems) => {
                            let mut args = vec![];
                            for (field_num, field_ty) in elems.iter().enumerate() {
                                let field_name = format!("tuple_{}", field_num);
                                let field = self.encoder.encode_raw_ref_field(
                                    field_name,
                                    field_ty.expect_ty()
                                )?;
                                args.push(
                                    self.encode_snap_arg(
                                        self.encode_arg_local(SNAPSHOT_ARG),
                                        field,
                                        field_ty.expect_ty()
                                    )?
                                );
                            }
                            args
                        }
                        _ => unreachable!()
                    }
                )
            )),
            snap_domain: Some(snap_domain),
        })
    }

    fn encode_snap_func_primitive(&self, field: vir::Field)
        -> EncodingResult<vir::Function>
    {
        let return_type = self.encoder.encode_value_type(self.ty)?;
        let body = self.encode_arg_field(
            self.encode_arg_local(SNAPSHOT_ARG),
            field
        );
        Ok(self.encode_snap_func(return_type, body))
    }

    fn encode_snap_func(&self, return_type: vir::Type, body: vir::Expr) -> vir::Function {
        let posts = 
        if prusti_common::config::enable_purification_optimization() {
            let self_var = vir::LocalVar{name: "__result".to_owned(), typ: return_type.clone()};
            let valid_func = snapshot::valid_func_for_type(&return_type);
            let self_arg = vir::Expr::local(self_var.clone());
            let valid_post = vir::Expr::domain_func_app(valid_func, vec![self_arg]); 
            vec![valid_post];
            vec![] //FIXME this should be the above vec but this currently doesn't verify
        }
        else {
            vec![]
        };

        vir::Function {
            name: SNAPSHOT_GET.to_string(),
            formal_args: vec![self.encode_arg_var(SNAPSHOT_ARG)],
            return_type: return_type.clone(),
            pres: vec![self.encode_predicate_access(
                self.encode_arg_local(SNAPSHOT_ARG)
            )],
            posts,
            body: Some(
                vir::Expr::wrap_in_unfolding(
                    self.encode_arg_local(SNAPSHOT_ARG),
                    body
                )
            ),
        }
    }

    fn encode_predicate_access(&self, expr: vir::Expr) -> vir::Expr {
        vir::Expr::predicate_access_predicate(
            self.predicate_name.clone(),
            expr,
            PermAmount::Read,
        )
    }

    fn encode_arg_local<S: Into<String>>(&self, arg_name: S) -> vir::Expr {
        vir::Expr::local(
            self.encode_arg_var(arg_name),
        )
    }

    fn encode_arg_field(&self, location: vir::Expr, field: vir::Field) -> vir::Expr {
        vir::Expr::field(
            location,
            field,
        )
    }

    fn encode_arg_var<S: Into<String>>(&self, arg_name: S) -> vir::LocalVar {
        vir::LocalVar::new(arg_name, self.get_predicate_type())
    }

    fn get_predicate_type(&self) -> vir::Type {
        vir::Type::TypedRef(self.predicate_name.clone())
    }

    fn encode_snap_domain(&self) -> EncodingResult<SnapshotDomain> {
        Ok(SnapshotDomain{
            domain: self.encode_domain()?,
            equals_func: self.encode_equals_func(),
            equals_func_ref: self.encode_equals_func_ref(),
            not_equals_func: self.encode_not_equals_func(),
            not_equals_func_ref: self.encode_not_equals_func_ref(),
        })
    }

    fn encode_snap_func_generic(&self, return_type: vir::Type) -> vir::Function {
        vir::Function {
            name: SNAPSHOT_GET.to_string(),
            formal_args: vec![self.encode_arg_var(SNAPSHOT_ARG)],
            return_type,
            pres: vec![],
            posts: vec![],
            body: None,
        }
    }

    fn encode_domain(&self) -> EncodingResult<vir::Domain> {
        let cons_func = self.encode_domain_cons()?;
        let cons_axiom_injectivity = self.encode_cons_injectivity(
            self.encode_injectivity_axiom_name(0),
            &cons_func,
        );

        Ok(vir::Domain {
            name: self.encode_domain_name(),
            functions: vec![cons_func],
            axioms: vec![cons_axiom_injectivity],
            type_vars: vec![]
        })
    }

    fn encode_domain_name(&self) -> String {
        format!(
            "{}{}",
            SNAPSHOT_DOMAIN_PREFIX,
            self.predicate_name,
        )
    }

    fn encode_domain_cons(&self)
        -> EncodingResult<vir::DomainFunc>
    {
        Ok(vir::DomainFunc {
            name: SNAPSHOT_CONS.to_string(),
            formal_args: self.encode_domain_cons_formal_args()?,
            return_type: vir::Type::Domain(self.encode_domain_name()),
            unique: false,
            domain_name: self.encode_domain_name(),
        })
    }

    fn encode_cons_injectivity(&self, axiom_name: String, cons_func: &vir::DomainFunc)
        -> vir::DomainAxiom
    {
        let (lhs_args, lhs_call) = self.encode_injectivity_args_call(
            cons_func,
            "_1".to_string()
        );

        let (rhs_args, rhs_call) = self.encode_injectivity_args_call(
            cons_func,
            "_2".to_string()
        );

        let mut vars = Vec::new();
        vars.extend(lhs_args.iter().cloned());
        vars.extend(rhs_args.iter().cloned());

        let conjunction = vir::ExprIterator::conjoin(
            &mut lhs_args.into_iter().zip(rhs_args.into_iter()).map(
                |(l,r)| vir::Expr::eq_cmp(
                    vir::Expr::local(l.clone()),
                    vir::Expr::local(r.clone())
                )
            )
        );

        let trigger = vir::Trigger::new(vec![lhs_call.clone(), rhs_call.clone()]);

        vir::DomainAxiom {
            name: axiom_name,
            expr: vir::Expr::forall(
                vars,
                vec![trigger],
                vir::Expr::implies(
                    vir::Expr::eq_cmp(
                        lhs_call,
                        rhs_call
                    ),
                    conjunction
                )
            ),
            domain_name: self.encode_domain_name(),
        }
    }

    fn encode_injectivity_axiom_name(&self, variant_index: i64) -> String {
        format!("{}$injectivity${}", self.encode_domain_name(), variant_index)
    }

    fn encode_injectivity_args_call(&self, cons_func: &vir::DomainFunc, suffix: String)
        -> (Vec<vir::LocalVar>, vir::Expr){
        let args: Vec<_> = cons_func.formal_args.iter().map(
            |v| vir::LocalVar::new(
                format!("{}{}", v.name.to_string(), suffix),
                v.typ.clone()
            )
        ).collect();

        let call = vir::Expr::domain_func_app(
            cons_func.clone(),
            args.iter().map(|v| vir::Expr::local(v.clone())).collect(),
        );

        (args, call)
    }

    pub fn encode_equals_func(&self) -> vir::Function {
        self.encode_cmp_func(SNAPSHOT_EQUALS.to_string(), vir::BinOpKind::EqCmp)
    }

    pub fn encode_not_equals_func(&self) -> vir::Function {
        self.encode_cmp_func(SNAPSHOT_NOT_EQUALS.to_string(), vir::BinOpKind::NeCmp)
    }

    fn encode_cmp_func(&self, name: String, cmp: vir::BinOpKind) -> vir::Function {
        vir::Function {
            name,
            formal_args: vec![
                self.encode_arg_var(SNAPSHOT_LEFT),
                self.encode_arg_var(SNAPSHOT_RIGHT),
            ],
            return_type: vir::Type::Bool,
            pres: vec![
                self.encode_predicate_access(
                    self.encode_arg_local(SNAPSHOT_LEFT)
                ),
                self.encode_predicate_access(
                    self.encode_arg_local(SNAPSHOT_RIGHT)
                ),
            ],
            posts: vec![],
            body: Some(vir::Expr::BinOp(
                cmp,
                box self.encode_value_snapshot_call(SNAPSHOT_LEFT),
                box self.encode_value_snapshot_call(SNAPSHOT_RIGHT),
                vir::Position::default(),
            )),
        }
    }

    fn encode_value_snapshot_call<S: Into<String>>(&self, arg_name: S) -> vir::Expr {
        let name = arg_name.into();
        self.encode_snapshot_call(
            name.clone(),
            self.encode_arg_local(name.clone())
        )
    }

    fn encode_snapshot_call<S: Into<String>>(&self, formal_arg_name: S, arg: vir::Expr) -> vir::Expr {
        let name = formal_arg_name.into();
        vir::Expr::func_app(
            SNAPSHOT_GET.to_string(),
            vec![arg],
            vec![self.encode_arg_var(name)],
            vir::Type::Domain(self.encode_domain_name()),
            vir::Position::default(),
        )
    }

    fn encode_domain_cons_formal_args(&self)
        -> EncodingResult<Vec<vir::LocalVar>>
    {
        let mut formal_args = vec![];
        match self.ty.kind() {
            ty::TyKind::Adt(adt_def, subst) if !adt_def.is_box() => {
                let tcx = self.encoder.env().tcx();
                let mut field_num = 0;
                for field in &adt_def.non_enum_variant().fields {
                    let field_ty = field.ty(tcx, subst);
                    let snapshot = self.encoder.encode_snapshot(&field_ty)?;
                    formal_args.push(
                        self.encode_local_var(field_num, &snapshot.get_type())
                    );
                    field_num += 1;
                }
            },

            ty::TyKind::Int(_)
            | ty::TyKind::Uint(_)
            | ty::TyKind::Char
            | ty::TyKind::Bool
            | ty::TyKind::Param(_) => {
                formal_args.push(self.encode_arg_var(SNAPSHOT_ARG))
            },

            ty::TyKind::Tuple(elems) => {
                for (field_num, field_ty) in elems.iter().enumerate() {
                    self.encoder.encode_snapshot(field_ty.expect_ty()); // ensure there is a snapshot
                    let field_type = self.encoder.encode_value_type(field_ty.expect_ty())?;
                    formal_args.push(
                        self.encode_local_var(field_num, &field_type)
                    );
                }
            }

            _ => unreachable!(), // note that ADTs are handled separately
        }
        Ok(formal_args)
    }

    fn encode_local_var(&self, counter: usize, field_type: &vir::Type) -> vir::LocalVar {
        let typ = match field_type.clone() {
            vir::Type::TypedRef(ref name) => {
                vir::Type::Domain(name.clone())
            },
            t => t,
        };
        let name = format!("{}_{}", SNAPSHOT_ARG, counter);
        vir::LocalVar::new(name, typ)
    }

    fn encode_cons_func_args(
        &self,
        variant_arg: vir::Expr,
        variant: &ty::VariantDef,
        subst: ty::subst::SubstsRef<'tcx>,
    ) -> EncodingResult<Vec<vir::Expr>>
    {
        let tcx = self.encoder.env().tcx();
        variant
            .fields
            .iter()
            .map(|f|
                self.encoder.encode_struct_field(
                    &f.ident.to_string(),
                    &f.ty(tcx, subst)
                ).and_then(|encoded_field|
                    self.encode_snap_arg(
                        variant_arg.clone(),
                        encoded_field,
                        &f.ty(tcx, subst)
                    )
                )
            ).collect::<Result<_, _>>()
    }

    fn encode_snap_arg(&self, location: vir::Expr, field: vir::Field, field_ty: ty::Ty<'tcx>)
        -> EncodingResult<vir::Expr>
    {
        let snapshot = self.encoder.encode_snapshot(field_ty)?;
        Ok(snapshot.snap_call(
            self.encode_arg_field(location, field)
        ))
    }

    pub fn encode_equals_func_ref(&self) -> vir::Function {
        self.encode_cmp_func_ref(SNAPSHOT_EQUALS.to_string(), vir::BinOpKind::EqCmp)
    }

    pub fn encode_not_equals_func_ref(&self) -> vir::Function {
        self.encode_cmp_func_ref(SNAPSHOT_NOT_EQUALS.to_string(),vir::BinOpKind::NeCmp)
    }

    fn encode_cmp_func_ref(&self, name: String, cmp: vir::BinOpKind) -> vir::Function {
        let arg_type = vir::Type::TypedRef(
            format!("ref${}", self.predicate_name)
        );
        let formal_left = vir::LocalVar::new(SNAPSHOT_LEFT, arg_type.clone());
        let formal_right = vir::LocalVar::new(SNAPSHOT_RIGHT, arg_type.clone());
        let arg_left = self.get_ref_field(formal_left.clone());
        let arg_right = self.get_ref_field(formal_right.clone());

        vir::Function {
            name,
            formal_args: vec![formal_left.clone(), formal_right.clone()],
            return_type: vir::Type::Bool,
            pres: vec![
                self.get_ref_field_perm(arg_left.clone()),
                self.encode_predicate_access(arg_left),
                self.get_ref_field_perm(arg_right.clone()),
                self.encode_predicate_access(arg_right),
            ],
            posts: vec![],
            body: Some(vir::Expr::BinOp(
                cmp,
                box self.encode_ref_snapshot_call(SNAPSHOT_LEFT),
                box self.encode_ref_snapshot_call(SNAPSHOT_RIGHT),
                vir::Position::default(),
            )),
        }
    }

    fn get_ref_field(&self, var: vir::LocalVar) -> vir::Expr {
        vir::Expr::field(
            vir::Expr::local(var),
            vir::Field::new("val_ref", self.get_predicate_type()),
        )
    }

    fn get_ref_field_perm(&self, expr: vir::Expr) -> vir::Expr {
        vir::Expr::field_access_predicate(
            expr,
            PermAmount::Read,
        )
    }

    fn encode_ref_snapshot_call<S: Into<String>>(&self, arg_name: S) -> vir::Expr {
        let name = arg_name.into();
        let arg = self.get_ref_field(self.encode_arg_var(name.to_string()));
        self.encode_snapshot_call(name, arg)
    }
}


impl<'s, 'v: 's, 'tcx: 'v> SnapshotAdtEncoder<'s, 'v, 'tcx> {
    pub fn new(
        snapshot_encoder: &'s SnapshotEncoder<'s, 'v, 'tcx>,
        adt_def: &'s ty::AdtDef,
        subst: ty::subst::SubstsRef<'tcx>,
    ) -> Self {
        SnapshotAdtEncoder {
            snapshot_encoder,
            adt_def,
            subst,
            predicate: snapshot_encoder
                .encoder
                .encode_type_predicate_def(snapshot_encoder.ty)
                .unwrap(),
        }
    }

    fn encode_snapshot(&self) -> EncodingResult<Snapshot> {
        let snap_domain = self.encode_snap_domain()?;
        let snap_func = self.encode_snap_func(&snap_domain)?;

        Ok(Snapshot {
            predicate_name: self.snapshot_encoder.predicate_name.clone(),
            snap_func: Some(snap_func),
            snap_domain: Some(snap_domain),
        })
    }

    fn encode_snap_domain(&self) -> EncodingResult<SnapshotDomain>
    {
        Ok(SnapshotDomain{
            domain: self.encode_domain()?,
            equals_func: self.snapshot_encoder.encode_equals_func(),
            equals_func_ref: self.snapshot_encoder.encode_equals_func_ref(),
            not_equals_func: self.snapshot_encoder.encode_not_equals_func(),
            not_equals_func_ref: self.snapshot_encoder.encode_not_equals_func_ref(),
        })
    }

    fn encode_domain(&self) -> EncodingResult<vir::Domain>
    {
        let mut functions = self.encode_constructors()?;
        let mut axioms = self.encode_axioms(&functions);

        if let Some((variant_func, variant_axiom)) = self.encode_variant_func_and_axioms() {
            functions.push(variant_func);
            axioms.push(variant_axiom);
        }



        if let Some((mut field_funcs, mut field_axioms)) = self.encode_field_funcs()? {
            functions.append(&mut field_funcs);
            axioms.append(&mut field_axioms);
        }

        if prusti_common::config::enable_purification_optimization() {
            let domain_name = self.snapshot_encoder.encode_domain_name();
            let valid_function = self.encode_valid_function();
            let valid_axiom = self.encode_valid_axiom()?;

            functions.push(snapshot::encode_unfold_witness(domain_name));
            functions.push(valid_function);
            axioms.push(valid_axiom);

        }


        Ok(vir::Domain {
            name: self.snapshot_encoder.encode_domain_name(),
            functions,
            axioms,
            type_vars: vec![]
        })
    }


    fn encode_valid_function(&self) -> vir::DomainFunc {
        let domain_name = self.snapshot_encoder.encode_domain_name();
        let domain_type = vir::Type::Domain(domain_name);
        snapshot::valid_func_for_type(&domain_type)
    }


    fn encode_valid_axiom(&self) -> EncodingResult<vir::DomainAxiom> {
        let domain_name = self.snapshot_encoder.encode_domain_name();

        let self_var = vir::LocalVar::new(
            "self",
            vir::Type::Domain(domain_name.to_string()),
        );

        let valid_func_apps: vir::Expr = self.adt_def.all_fields().map(|field| {
            let field_type = self.compute_vir_type_for_field(field).unwrap(); //TODO don't unwrap
            let field_name = field.ident.name.to_ident_string();


            let field_func = snapshot::encode_field_domain_func(field_type.clone(), field_name, domain_name.clone());
            let field_func_app = vir::Expr::domain_func_app(field_func, vec![vir::Expr::local(self_var.clone())]); 

            let valid_func = snapshot::valid_func_for_type(&field_type);
            vir::Expr::domain_func_app(valid_func, vec![field_func_app])
        })
       .fold(true.into(),  vir::Expr::and);

        
       let expr = vir::Expr::forall( vec![self_var], vec![], valid_func_apps); //TODO triggers
        Ok(vir::DomainAxiom {
            name: format!("{}$valid$axiom", domain_name).to_string(), 
            expr,
            domain_name,
        })
    }
    

    fn encode_field_domain_func(
        &self,
        field: &ty::FieldDef,
    ) -> EncodingResult<vir::DomainFunc> {
        let domain_name = self.snapshot_encoder.encode_domain_name();
        let field_type = self.compute_vir_type_for_field(field)?;
        let field_name = field.ident.name.to_ident_string();

        Ok(snapshot::encode_field_domain_func(
            field_type,
            field_name,
            domain_name,
        ))
    }

    fn compute_vir_type_for_field(
        &self,
        field: &ty::FieldDef,
    ) -> EncodingResult<vir::Type> {
        let tcx = self.snapshot_encoder.encoder.env().tcx();
        let field_ty = field.ty(tcx, self.subst);
        let snapshot = self.snapshot_encoder.encoder.encode_snapshot(&field_ty)?;
        Ok(snapshot.get_type())
    }

    fn encode_field_domain_axiom(
        &self,
        field: &ty::FieldDef,
    ) -> EncodingResult<vir::DomainAxiom> {
        let domain_name = self.snapshot_encoder.encode_domain_name();

        let this_field_name = field.ident.name.to_ident_string();
        let this_field_type = self.compute_vir_type_for_field(field)?;
        let this_field: vir::LocalVar = vir::LocalVar {
            typ: this_field_type,
            name: this_field_name.clone(),
        };
        let this_field_func: vir::DomainFunc = self.encode_field_domain_func(field)?;

        let all_fields: EncodingResult<Vec<vir::LocalVar>> = self
            .adt_def
            .all_fields()
            .map(|f| {
                let field_name = f.ident.name.to_ident_string();
                let field_type = self.compute_vir_type_for_field(f)?;
                Ok(vir::LocalVar {
                    name: field_name,
                    typ: field_type.clone(),
                })
            })
            .collect();
        let all_fields: Vec<vir::LocalVar> = all_fields?;
        let all_field_exprs: Vec<vir::Expr> =
            all_fields.iter().cloned().map(vir::Expr::local).collect();

        let constructors = self.encode_constructors()?;
        //TODO handle enums
        let constructor_func = constructors[0].clone();
        let constructor_call = vir::Expr::domain_func_app(constructor_func, all_field_exprs);

        let field_of_cons =
            vir::Expr::domain_func_app(this_field_func.clone(), vec![constructor_call.clone()]);
        let triggers: Vec<vir::Trigger> = vec![vir::Trigger::new(vec![field_of_cons.clone()])];
        let forall_body = vir::Expr::eq_cmp(field_of_cons, vir::Expr::local(this_field));
        let axiom_body: vir::Expr = vir::Expr::forall(all_fields, triggers, forall_body);

        Ok(vir::DomainAxiom {
            name: format!("{}${}$axiom", domain_name, this_field_name),
            expr: axiom_body,
            domain_name: domain_name.clone(),
        })
    }

    /// Encodes and returns the functions and axioms for each field of this struct
    fn encode_field_funcs(
        &self,
    ) -> EncodingResult<Option<(Vec<vir::DomainFunc>, Vec<vir::DomainAxiom>)>> {
        if self.adt_def.is_struct() {
            let domain_name = self.snapshot_encoder.encode_domain_name();

            let mut funcs = vec![];
            let mut axioms = vec![];

            for field in self.adt_def.all_fields() {
                funcs.push(self.encode_field_domain_func(field)?);
                axioms.push(self.encode_field_domain_axiom(field)?);
            }

            Ok(Some((funcs, axioms)))
        } else {
            Ok(None)
        }
    }


    fn encode_variant_func_and_axioms(&self)
        -> Option<(vir::DomainFunc, vir::DomainAxiom)>
    {
        if self.adt_def.is_enum() {
            let variant_func = self.encode_variant_func();
            let variant_axiom = self.encode_axiom_variants(&variant_func);
            Some((variant_func, variant_axiom))
        } else {
            None
        }
    }

    fn encode_variant_func(&self) -> vir::DomainFunc
    {
        let domain_name = self.snapshot_encoder.encode_domain_name();
        let snap_type = vir::Type::Domain(domain_name.to_string());
        let arg = vir::LocalVar::new("self", snap_type);
        vir::DomainFunc {
            name: SNAPSHOT_VARIANT.to_string(),
            formal_args: vec![arg],
            return_type: vir::Type::Int,
            unique: false,
            domain_name: domain_name.to_string(),
        }
    }

    fn encode_axiom_variants(
        &self,
        variant_func: &vir::DomainFunc,
    ) -> vir::DomainAxiom {

        let domain_name = self.snapshot_encoder.encode_domain_name();
        let var = vir::LocalVar::new(
            SNAPSHOT_ARG,
            vir::Type::Domain(domain_name.to_string()),
        );
        let variant_call = vir::Expr::domain_func_app(
            variant_func.clone(),
            vec![vir::Expr::local(var.clone())],
        );

        let variant_range = self.adt_def.variant_range();
        let start = vir::Expr::from(variant_range.start.as_usize());
        let end = vir::Expr::from(variant_range.end.as_usize());

        vir::DomainAxiom {
            name: format!("{}$variants", domain_name.to_string()),
            expr: vir::Expr::forall(
                vec![var],
                vec![vir::Trigger::new(vec![variant_call.clone()])],
                vir::Expr::and(
                    vir::Expr::le_cmp(start, variant_call.clone()),
                    vir::Expr::lt_cmp(variant_call, end)
                )
            ),
            domain_name: domain_name.to_string()
        }
    }

    fn encode_constructors(&self) -> EncodingResult<Vec<vir::DomainFunc>>
    {
        let domain_name = self.snapshot_encoder.encode_domain_name();
        let mut result = vec![];
        for (variant_index, variant_def) in self.adt_def.variants.iter().enumerate() {
            result.push(
                vir::DomainFunc {
                    name: self.encode_constructor_name(variant_index),
                    formal_args: self.encode_constructor_args(variant_def)?,
                    return_type: vir::Type::Domain(domain_name.to_string()),
                    unique: false,
                    domain_name: domain_name.to_string(),
                }
            )
        }

        Ok(result)
    }

    fn encode_constructor_args(
        &self,
        variant_def: &ty::VariantDef
    ) -> EncodingResult<Vec<vir::LocalVar>>
    {
        let mut formal_args = vec![];
        let tcx = self.snapshot_encoder.encoder.env().tcx();
        let mut field_num = 0;
        for field in &variant_def.fields {
            let field_ty = field.ty(tcx, self.subst);
            let snapshot = self.snapshot_encoder.encoder.encode_snapshot(&field_ty)?;
            formal_args.push(
                self.snapshot_encoder.encode_local_var(field_num, &snapshot.get_type())
            );
            field_num += 1;
        }
        Ok(formal_args)
    }

    fn encode_constructor_name(&self, variant_index: usize) -> String {
        format!(
            "{}{}$",
            SNAPSHOT_CONS,
            variant_index,
        )
    }

    fn encode_axioms(
        &self,
        constructors: &Vec<vir::DomainFunc>,
    ) -> Vec<vir::DomainAxiom>
    {
        let mut result = vec![];
        for (variant_index, cons_func) in constructors.iter().enumerate() {
            result.push(self.snapshot_encoder.encode_cons_injectivity(
                self.snapshot_encoder.encode_injectivity_axiom_name(variant_index as i64),
                &cons_func
            ))
        }

        result
    }

    fn encode_snap_func(
        &self,
        snap_domain: &SnapshotDomain,
    ) -> EncodingResult<vir::Function>
    {
        if self.adt_def.variants.is_empty() {
            return Ok(vir::Function {
                name: SNAPSHOT_GET.to_string(),
                formal_args: vec![self.snapshot_encoder.encode_arg_var(SNAPSHOT_ARG)],
                return_type: snap_domain.get_type(),
                pres: vec![],
                posts: vec![],
                body: None
            })
        }

        let body = if self.adt_def.is_struct() {
            snap_domain.call_cons_func(
                self.snapshot_encoder.encode_cons_func_args(
                    self.snapshot_encoder.encode_arg_local(SNAPSHOT_ARG),
                    self.adt_def.non_enum_variant(),
                    self.subst,
                )?
            )
        } else if self.adt_def.variants.is_empty() {
            unimplemented!("CMFIXME")
        } else {
            let variant_arg = vir::Expr::field(
                self.snapshot_encoder.encode_arg_local(SNAPSHOT_ARG),
                self.snapshot_encoder.encoder.encode_discriminant_field(),
            );

            self.fold_snap_func_conditional(
                snap_domain,
                variant_arg,
                0,
            )?
        };

        Ok(
            self.snapshot_encoder.encode_snap_func(
                snap_domain.get_type(),
                body,
            )
        )
    }

    fn fold_snap_func_conditional(
        &self,
        snap_domain: &SnapshotDomain,
        variant_arg: vir::Expr,
        index: usize,
    ) -> EncodingResult<vir::Expr>
    {
        if index >= self.adt_def.variants.len() - 1 {
            self.encode_snap_variant(snap_domain, index)
        } else {
            let tcx = self.snapshot_encoder.encoder.env().tcx();
            let variant_index = self.adt_def.discriminant_for_variant(
                tcx,
                rustc_target::abi::VariantIdx::from_usize(index)
            ).val;
            let size = ty::tls::with(|tcx| Integer::from_attr(&tcx, self.adt_def.repr.discr_type()).size());
            let discriminant = size.sign_extend(variant_index) as i128;

            Ok(vir::Expr::ite(
                vir::Expr::eq_cmp(
                    variant_arg.clone(),
                    vir::Expr::from(discriminant),
                ),
                self.encode_snap_variant(snap_domain, index)?,
                self.fold_snap_func_conditional(
                    snap_domain,
                    variant_arg,
                    index+1,
                )?,
            ))
        }
    }

    fn encode_snap_variant(
        &self,
        snap_domain: &SnapshotDomain,
        variant_index: usize,
    ) -> EncodingResult<vir::Expr>
    {
        let (
                variant_location,
                predicate_name,
                variant,
                enum_variant_index
        ) = self.obtain_variant(variant_index)?;

        let cons_func = snap_domain.domain.functions[variant_index].clone();

        if variant.fields.is_empty() {
            Ok(vir::Expr::domain_func_app(cons_func, vec![]))
        } else {
            let args = self.snapshot_encoder.encode_cons_func_args(
                variant_location.clone(),
                variant,
                self.subst
            )?;
            Ok(
                vir::Expr::unfolding(
                    predicate_name,
                    vec![variant_location],
                    vir::Expr::domain_func_app(cons_func, args),
                    vir::PermAmount::Read,
                    enum_variant_index,
                )
            )
        }
    }

    fn obtain_variant(&self, variant_index: usize)
        -> EncodingResult<(vir::Expr, String, &ty::VariantDef, vir::MaybeEnumVariantIndex)>
    {
        match &self.predicate {
            vir::Predicate::Enum(enum_predicate) => {
                let (_, variant_name, _) = enum_predicate.variants[variant_index].clone();
                Ok((
                    self.snapshot_encoder
                        .encode_arg_local(SNAPSHOT_ARG)
                        .variant(variant_name.borrow()),
                    format!("{}{}", self.snapshot_encoder.predicate_name.to_string(), variant_name.to_string()),
                    &self.adt_def.variants[rustc_target::abi::VariantIdx::from_usize(variant_index)],
                    Some(EnumVariantIndex::new(variant_name.to_string())),
                ))
            }
            vir::Predicate::Struct(_) => {
                debug_assert_eq!(variant_index, 0);
                Ok((
                    self.snapshot_encoder.encode_arg_local(SNAPSHOT_ARG),
                    self.snapshot_encoder.predicate_name.to_string(),
                    // Notice that we *cannot* use &self.adt_def.non_enum_variant()
                    // here as an enum with just one variant is internally treated as a struct
                    &self.adt_def.variants[rustc_target::abi::VariantIdx::from_usize(variant_index)],
                    None,
                ))
            }
            _ => {
                Err(EncodingError::incorrect(
                    "predicate does not correspond to an enum or struct".to_string()
                ))
            }
        }
    }
}

