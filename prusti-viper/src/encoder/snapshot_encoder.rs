// © 2020, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use prusti_common::vir;
use crate::encoder::Encoder;
use rustc_middle::ty;
use prusti_common::vir::{PermAmount};
use log::warn;


const SNAPSHOT_DOMAIN_PREFIX: &str = "Snap$";
const SNAPSHOT_CONS: &str = "cons$";
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

#[derive(Clone)]
pub struct SnapshotDomain {
    pub domain: vir::Domain,
    pub equals_func: vir::Function,
    pub equals_func_ref: vir::Function,
    pub not_equals_func: vir::Function,
    pub not_equals_func_ref: vir::Function,
}

impl SnapshotDomain {
    pub fn get_type(&self) -> vir::Type {
        self.domain.functions[0].return_type.clone()
    }

    pub fn call_snap_func(&self, args: Vec<vir::Expr>) -> vir::Expr {
        let cons_function = self.domain.functions[0].clone();
        vir::Expr::DomainFuncApp(cons_function, args, vir::Position::default())
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

#[derive(Clone)]
pub struct Snapshot {
    pub predicate_name: String,
    pub snap_func: Option<vir::Function>,
    pub snap_domain: Option<SnapshotDomain>, // for types with fields
}

impl Snapshot {

    pub fn is_defined(&self) -> bool {
        self.snap_func.is_some()
    }

    pub fn get_domain(&self) -> Option<vir::Domain> {
        match &self.snap_domain {
            Some(s) => Some(s.domain.clone()),
            None => None,
        }
    }

    pub fn get_functions(&self) -> Vec<vir::Function> {
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

    pub fn get_snap_name(&self) -> String {
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

    pub fn get_equals_func_name(&self) -> String {
        SNAPSHOT_EQUALS.to_string()
    }

    pub fn get_not_equals_func_name(&self) -> String {
        SNAPSHOT_NOT_EQUALS.to_string()
    }

    pub fn get_snap_call(&self, arg: vir::Expr) -> vir::Expr {
        match &self.snap_func {
            Some(func) => {
                vir::Expr::FuncApp(
                    self.get_snap_name(),
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
        vir::Expr::BinOp(
            vir::BinOpKind::EqCmp,
            Box::new(self.get_snap_call(lhs)),
            Box::new(self.get_snap_call(rhs)),
            pos,
        )
    }

    pub fn encode_not_equals(&self, lhs: vir::Expr, rhs: vir::Expr, pos: vir::Position) -> vir::Expr {
        vir::Expr::BinOp(
            vir::BinOpKind::NeCmp,
            Box::new(self.get_snap_call(lhs)),
            Box::new(self.get_snap_call(rhs)),
            pos,
        )
    }
}

impl<'p, 'v, 'r: 'v, 'a: 'r, 'tcx: 'a> SnapshotEncoder<'p, 'v, 'tcx> {
    pub fn new(encoder: &'p Encoder<'v, 'tcx>, ty: ty::Ty<'tcx>, predicate_name: String) -> Self {
        SnapshotEncoder { encoder, ty, predicate_name }
    }

    pub fn encode(&self) -> Snapshot {
        if !self.is_supported() {
            return Snapshot {
                predicate_name: self.predicate_name.clone(),
                snap_func: None,
                snap_domain: None,
            }
        }

        match &self.ty.kind {
            ty::TyKind::Int(_)
            | ty::TyKind::Uint(_)
            | ty::TyKind::Char
            | ty::TyKind::Bool => {
                self.encode_snap_primitive(
                    self.encoder.encode_value_field(self.ty)
                )
            }
            ty::TyKind::Param(_) => {
                self.encode_snap_generic()
            }
            ty::TyKind::Adt(adt_def, _) if !adt_def.is_box() => {
                if adt_def.variants.len() != 1 {
                    warn!("Generating equality tests for enums is not supported yet");
                }
                self.encode_snap_struct()
            }
            ty::TyKind::Tuple(_) => {
                self.encode_snap_struct()
            }

            x => unimplemented!("{:?}", x),
        }
    }

    fn is_supported(&self) -> bool {
        self.is_ty_supported(self.ty)
    }

    fn is_ty_supported(&self, ty: ty::Ty<'tcx>) -> bool {
        match ty.kind {
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
                if adt_def.variants.len() > 1 {
                    return false
                }
                let tcx = self.encoder.env().tcx();
                for field in &adt_def.non_enum_variant().fields {
                    let field_ty = field.ty(tcx, subst);
                    if !self.is_ty_supported(field_ty) {
                        return false
                    }
                }
                true
            }
            ty::TyKind::Tuple(elems) => {
                for field_ty in elems {
                    if !self.is_ty_supported(field_ty.expect_ty()) {
                        return false
                    }
                }
                true
            }
            _ => false
        }
    }

    fn encode_snap_primitive(&self, field: vir::Field) -> Snapshot {
        Snapshot {
            predicate_name: self.predicate_name.clone(),
            snap_func: Some(self.encode_snap_func_primitive(field)),
            snap_domain: None,
        }
    }

    fn encode_snap_func_primitive(&self, field: vir::Field) -> vir::Function {
        let return_type = self.encoder.encode_value_type(self.ty);
        let body = self.encode_snap_arg_field(field);
        self.encode_snap_func(return_type, body)
    }
    fn encode_snap_func(&self, return_type: vir::Type, body: vir::Expr) -> vir::Function {
        vir::Function {
            name: SNAPSHOT_GET.to_string(),
            formal_args: vec![self.encode_snap_arg_var(SNAPSHOT_ARG)],
            return_type: return_type.clone(),
            pres: vec![self.encode_snap_predicate_access(
                self.encode_snap_arg_local(SNAPSHOT_ARG)
            )],
            posts: vec![],
            body: Some(vir::Expr::Unfolding(
                self.predicate_name.clone(),
                vec![self.encode_snap_arg_local(SNAPSHOT_ARG)],
                Box::new(body),
                vir::PermAmount::Read,
                None,
                vir::Position::default(),
            )),
        }
    }

    fn encode_snap_predicate_access(&self, expr: vir::Expr) -> vir::Expr {
        vir::Expr::PredicateAccessPredicate(
            self.predicate_name.clone(),
            Box::new(expr),
            PermAmount::Read,
            vir::Position::default()
        )
    }

    fn encode_snap_arg_local<S: Into<String>>(&self, arg_name: S) -> vir::Expr {
        vir::Expr::Local(
            self.encode_snap_arg_var(arg_name),
            vir::Position::default()
        )
    }

    fn encode_snap_arg_field(&self, field: vir::Field) -> vir::Expr {
        vir::Expr::Field(
            Box::new(self.encode_snap_arg_local(SNAPSHOT_ARG)),
            field,
            vir::Position::default()
        )
    }

    fn encode_snap_arg_var<S: Into<String>>(&self, arg_name: S) -> vir::LocalVar {
        vir::LocalVar::new(arg_name, self.get_predicate_type())
    }

    fn get_predicate_type(&self) -> vir::Type {
        vir::Type::TypedRef(self.predicate_name.clone())
    }

    fn encode_snap_generic(&self) -> Snapshot {
        let snap_domain = self.encode_snap_domain();
        Snapshot {
            predicate_name: self.predicate_name.clone(),
            snap_func: Some(self.encode_snap_func_generic(snap_domain.get_type())),
            snap_domain: Some(snap_domain),
        }
    }

    fn encode_snap_domain(&self) -> SnapshotDomain {
        SnapshotDomain{
            domain: self.encode_domain(),
            equals_func: self.encode_equals_func(),
            equals_func_ref: self.encode_equals_func_ref(),
            not_equals_func: self.encode_not_equals_func(),
            not_equals_func_ref: self.encode_not_equals_func_ref(),
        }
    }

    fn encode_snap_func_generic(&self, return_type: vir::Type) -> vir::Function {
        vir::Function {
            name: SNAPSHOT_GET.to_string(),
            formal_args: vec![self.encode_snap_arg_var(SNAPSHOT_ARG)],
            return_type,
            pres: vec![],
            posts: vec![],
            body: None,
        }
    }

    fn encode_snap_struct(&self) -> Snapshot {
        let snap_domain = self.encode_snap_domain();
        Snapshot {
            predicate_name: self.predicate_name.clone(),
            snap_func: Some(self.encode_snap_func(
                snap_domain.get_type(),
                snap_domain.call_snap_func(
                    self.encode_snap_func_args()
                )
            )),
            snap_domain: Some(snap_domain),
        }
    }

    fn encode_domain(&self) -> vir::Domain {
        let domain_name = self.encode_domain_name();
        let cons_func = self.encode_domain_cons(&domain_name);
        let cons_axiom_injectivity = self.encode_cons_injectivity(&domain_name, &cons_func);

        vir::Domain {
            name: domain_name,
            functions: vec![cons_func],
            axioms: vec![cons_axiom_injectivity],
            type_vars: vec![]
        }
    }

    fn encode_domain_name(&self) -> String {
        format!(
            "{}{}",
            SNAPSHOT_DOMAIN_PREFIX,
            self.predicate_name,
        )
    }

    fn encode_domain_cons(&self, domain_name: &String) -> vir::DomainFunc {
        vir::DomainFunc {
            name: SNAPSHOT_CONS.to_string(),
            formal_args: self.encode_domain_cons_formal_args(),
            return_type: vir::Type::Domain(domain_name.to_string()),
            unique: false,
            domain_name: domain_name.to_string(),
        }
    }

    fn encode_cons_injectivity(&self, domain_name: &String, cons_func: &vir::DomainFunc) -> vir::DomainAxiom {
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
            name: format!("{}$injectivity", domain_name.to_string()),
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
            domain_name: domain_name.to_string()
        }
    }

    fn encode_injectivity_args_call(&self, cons_func: &vir::DomainFunc, suffix: String)
        -> (Vec<vir::LocalVar>, vir::Expr){
        let args: Vec<_> = cons_func.formal_args.iter().map(
            |v| vir::LocalVar::new(
                format!("{}{}", v.name.to_string(), suffix),
                v.typ.clone()
            )
        ).collect();

        let call = vir::Expr::DomainFuncApp(
            cons_func.clone(),
            args.iter().map(|v| vir::Expr::local(v.clone())).collect(),
            vir::Position::default()
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
                self.encode_snap_arg_var(SNAPSHOT_LEFT),
                self.encode_snap_arg_var(SNAPSHOT_RIGHT),
            ],
            return_type: vir::Type::Bool,
            pres: vec![
                self.encode_snap_predicate_access(
                    self.encode_snap_arg_local(SNAPSHOT_LEFT)
                ),
                self.encode_snap_predicate_access(
                    self.encode_snap_arg_local(SNAPSHOT_RIGHT)
                ),
            ],
            posts: vec![],
            body: Some(vir::Expr::BinOp(
                cmp,
                Box::new(self.encode_value_snapshot_call(SNAPSHOT_LEFT)),
                Box::new(self.encode_value_snapshot_call(SNAPSHOT_RIGHT)),
                vir::Position::default(),
            )),
        }
    }

    fn encode_value_snapshot_call<S: Into<String>>(&self, arg_name: S) -> vir::Expr {
        let name = arg_name.into();
        self.encode_snapshot_call(
            name.clone(),
            self.encode_snap_arg_local(name.clone())
        )
    }

    fn encode_snapshot_call<S: Into<String>>(&self, formal_arg_name: S, arg: vir::Expr) -> vir::Expr {
        let name = formal_arg_name.into();
        vir::Expr::FuncApp(
            SNAPSHOT_GET.to_string(),
            vec![arg],
            vec![self.encode_snap_arg_var(name)],
            vir::Type::Domain(self.encode_domain_name()),
            vir::Position::default(),
        )
    }

    fn encode_domain_cons_formal_args(&self) -> Vec<vir::LocalVar> {
        let mut formal_args = vec![];
        match self.ty.kind {
            ty::TyKind::Adt(adt_def, subst) if !adt_def.is_box() => {
                let tcx = self.encoder.env().tcx();
                let mut field_num = 0;
                for field in &adt_def.non_enum_variant().fields {
                    let field_ty = field.ty(tcx, subst);
                    let snapshot = self.encoder.encode_snapshot(&field_ty);
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
                formal_args.push(self.encode_snap_arg_var(SNAPSHOT_ARG))
            },

            ty::TyKind::Tuple(elems) => {
                for (field_num, field_ty) in elems.iter().enumerate() {
                    self.encoder.encode_snapshot(field_ty.expect_ty()); // ensure there is a snapshot
                    let field_type = self.encoder.encode_value_type(field_ty.expect_ty());
                    formal_args.push(
                        self.encode_local_var(field_num, &field_type)
                    );
                }
            }

            _ => unreachable!(),
        }
        formal_args
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

    fn encode_snap_func_args(&self) -> Vec<vir::Expr> {
        match self.ty.kind {
            ty::TyKind::Adt(adt_def, subst) if !adt_def.is_box() => {
                let tcx = self.encoder.env().tcx();
                adt_def.non_enum_variant()
                    .fields
                    .iter()
                    .map(|f| self.encode_snap_arg(
                        self.encoder.encode_struct_field(
                            &f.ident.to_string(),
                            &f.ty(tcx, subst)
                            ),
                        &f.ty(tcx, subst),
                        )
                    ).collect()
            },
            ty::TyKind::Int(_)
            | ty::TyKind::Uint(_)
            | ty::TyKind::Char
            | ty::TyKind::Bool => {
                vec![self.encode_snap_arg_local(SNAPSHOT_ARG)]
            },

            ty::TyKind::Tuple(elems) => {
                let mut args = vec![];
                for (field_num, field_ty) in elems.iter().enumerate() {
                    let field_name = format!("tuple_{}", field_num);
                    let field = self.encoder.encode_raw_ref_field(field_name, field_ty.expect_ty());
                    args.push(
                        self.encode_snap_arg(field, field_ty.expect_ty())
                    );
                }
                args
            }

            _ => unreachable!(),
        }
    }

    fn encode_snap_arg(&self, field: vir::Field, field_ty: ty::Ty<'tcx>) -> vir::Expr {
        let snapshot = self.encoder.encode_snapshot(field_ty);
        snapshot.get_snap_call(
            self.encode_snap_arg_field(field)
        )
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
                self.encode_snap_predicate_access(arg_left),
                self.get_ref_field_perm(arg_right.clone()),
                self.encode_snap_predicate_access(arg_right),
            ],
            posts: vec![],
            body: Some(vir::Expr::BinOp(
                cmp,
                Box::new(self.encode_ref_snapshot_call(SNAPSHOT_LEFT)),
                Box::new(self.encode_ref_snapshot_call(SNAPSHOT_RIGHT)),
                vir::Position::default(),
            )),
        }
    }

    fn get_ref_field(&self, var: vir::LocalVar) -> vir::Expr {
        vir::Expr::Field(
            Box::new(vir::Expr::Local(var, vir::Position::default())),
            vir::Field::new("val_ref", self.get_predicate_type()),
            vir::Position::default()
        )
    }

    fn get_ref_field_perm(&self, expr: vir::Expr) -> vir::Expr {
        vir::Expr::FieldAccessPredicate(
            Box::new(expr),
            PermAmount::Read,
            vir::Position::default()
        )
    }

    fn encode_ref_snapshot_call<S: Into<String>>(&self, arg_name: S) -> vir::Expr {
        let name = arg_name.into();
        let arg = self.get_ref_field(self.encode_snap_arg_var(name.to_string()));
        self.encode_snapshot_call(name, arg)
    }
}
