// © 2020, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use prusti_common::vir;
use encoder::Encoder;
use rustc::ty;
use prusti_common::vir::{PermAmount, Type};


const SNAPSHOT_DOMAIN_PREFIX: &str = "Snap$";
const SNAPSHOT_CONS: &str = "cons$";
const SNAPSHOT_GET: &str = "snap$";
pub const SNAPSHOT_EQUALS: &str = "equals$";
const SNAPSHOT_ARG: &str = "_arg";
const SNAPSHOT_LEFT: &str = "_left";
const SNAPSHOT_RIGHT: &str = "_right";

pub struct SnapshotEncoder<'p, 'v: 'p, 'r: 'v, 'a: 'r, 'tcx: 'a> {
    encoder: &'p Encoder<'v, 'r, 'a, 'tcx>,
    ty: ty::Ty<'tcx>,
    predicate_name: String,

}

pub struct SnapshotDomain {
    pub domain: vir::Domain,
    pub equals_func: vir::Function,
    pub equals_func_ref: vir::Function,
}

impl SnapshotDomain {
    pub fn get_type(&self) -> vir::Type {
        self.domain.functions[0].return_type.clone()
    }

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
}

pub struct Snapshot {
    pub predicate_name: String,
    pub snap_func: vir::Function,
    pub snap_domain: Option<SnapshotDomain>, // for types with fields
}

impl Snapshot {

    pub fn get_domain(&self) -> Option<vir::Domain> {
        match &self.snap_domain {
            Some(s) => Some(s.domain.clone()),
            None => None,
        }
    }

    pub fn get_functions(&self) -> Vec<vir::Function> {
        let mut res = vec![self.snap_func.clone()];
        if let Some(s) = &self.snap_domain {
            res.push(s.equals_func.clone());
            res.push(s.equals_func_ref.clone());
        }
        res
    }

    pub fn get_snap_name(&self) -> String {
        self.snap_func.name.clone()
    }

    pub fn get_type(&self) -> vir::Type {
        self.snap_func.return_type.clone()
    }

    pub fn is_adt(&self) -> bool {
        self.snap_domain.is_some()
    }

    pub fn get_equals_func(&self) -> (String, vir::Function) {
        match &self.snap_domain {
            Some(s) => (self.predicate_name.clone(), s.equals_func.clone()),
            None => unreachable!()
        }
    }

    pub fn get_equals_func_ref(&self) -> (String, vir::Function) {
        match &self.snap_domain {
            Some(s) => {
                (get_ref_predicate_name(&self.predicate_name), s.equals_func_ref.clone())
            },
            None => unreachable!()
        }
    }
}

fn get_ref_predicate_name(predicate_name: &String) -> String {
    format!("ref${}", predicate_name.clone())
}

impl<'p, 'v, 'r: 'v, 'a: 'r, 'tcx: 'a> SnapshotEncoder<'p, 'v, 'r, 'a, 'tcx> {
    pub fn new(encoder: &'p Encoder<'v, 'r, 'a, 'tcx>, ty: ty::Ty<'tcx>, predicate_name: String) -> Self {
        SnapshotEncoder { encoder, ty, predicate_name }
    }

    pub fn encode(&self) -> Snapshot {
        match &self.ty.sty {
            ty::TypeVariants::TyInt(_) | ty::TypeVariants::TyUint(_) | ty::TypeVariants::TyChar => {
                self.encode_snap_primitive(
                    vir::Field::new("val_int", vir::Type::Int)
                )
            }
            ty::TypeVariants::TyBool => {
                self.encode_snap_primitive(
                    vir::Field::new("val_bool", vir::Type::Bool)
                )
            }
            ty::TypeVariants::TyParam(_) => {
                self.encode_snap_generic()
            }
            ty::TypeVariants::TyAdt(adt_def, _) if !adt_def.is_box() => {
                if adt_def.variants.len() != 1 {
                    warn!("Generating equality tests for enums is not supported yet");
                }
                self.encode_snap_struct()
            }
            ty::TypeVariants::TyTuple(_) => {
                self.encode_snap_struct()
            }

            x => unimplemented!("{:?}", x),
        }
    }

    fn encode_snap_primitive(&self, field: vir::Field) -> Snapshot {
        Snapshot {
            predicate_name: self.predicate_name.clone(),
            snap_func: self.encode_snap_func_primitive(field),
            snap_domain: None,
        }
    }

    fn encode_snap_func_primitive(&self, field: vir::Field) -> vir::Function {
        let return_type = self.encoder.encode_value_type(self.ty);
        let body = vir::Expr::Field(
            Box::new(self.encode_snap_arg_local(SNAPSHOT_ARG)),
            field,
            vir::Position::default()
        );
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
            vir::Position::default())
    }

    fn encode_snap_arg_local<S: Into<String>>(&self, arg_name: S) -> vir::Expr {
        vir::Expr::Local(
            self.encode_snap_arg_var(arg_name),
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
            snap_func: self.encode_snap_func_generic(snap_domain.get_type()),
            snap_domain: Some(snap_domain),
        }
    }

    fn encode_snap_domain(&self) -> SnapshotDomain {
        SnapshotDomain{
            domain: self.encode_domain(),
            equals_func: self.encode_equals_func(),
            equals_func_ref: self.encode_equals_func_ref(),
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
            snap_func: self.encode_snap_func(
                snap_domain.get_type(),
                snap_domain.call_snap_func(
                    self.encode_snap_func_args()
                )
            ),
            snap_domain: Some(snap_domain),
        }
    }

    fn encode_domain(&self) -> vir::Domain {
        vir::Domain {
            name: self.encode_domain_name(),
            functions: self.encode_domain_cons(),
            axioms: vec![],
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

    fn encode_domain_cons(&self) -> Vec<vir::DomainFunc> {
        let domain_name = self.encode_domain_name();
        let cons_fun = vir::DomainFunc {
            name: SNAPSHOT_CONS.to_string(),
            formal_args: self.encode_domain_cons_formal_args(),
            return_type: vir::Type::Domain(domain_name.clone()),
            unique: false,
            domain_name,
        };
        vec![cons_fun]
    }
    pub fn encode_equals_func(&self) -> vir::Function {
        vir::Function {
            name: SNAPSHOT_EQUALS.to_string(),
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
                vir::BinOpKind::EqCmp,
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
        match self.ty.sty {
            ty::TypeVariants::TyAdt(adt_def, subst) if !adt_def.is_box() => {
                // TODO so far this is for structs only
                let tcx = self.encoder.env().tcx();
                let mut field_num = 0;
                for field in &adt_def.variants[0].fields {
                    let field_ty = field.ty(tcx, subst);
                    self.encoder.encode_snapshot(field_ty);
                    let field_type = &self.encoder.encode_value_type(field.ty(tcx, subst));
                    formal_args.push(
                        self.encode_local_var(field_num, field_type)
                    );
                    field_num += 1;
                }
            },

            ty::TypeVariants::TyInt(_)
            | ty::TypeVariants::TyUint(_)
            | ty::TypeVariants::TyChar
            | ty::TypeVariants::TyBool
            | ty::TypeVariants::TyParam(_) => {
                formal_args.push(self.encode_snap_arg_var(SNAPSHOT_ARG))
            },

            ty::TypeVariants::TyTuple(elems) => {
                for (field_num, field_ty) in elems.iter().enumerate() {
                    let field_type = self.encoder.encode_value_type(field_ty);
                    self.encoder.encode_snapshot(field_ty);
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
        match self.ty.sty {
            ty::TypeVariants::TyAdt(adt_def, subst) if !adt_def.is_box() => {
                // TODO so far this works only for structs
                let tcx = self.encoder.env().tcx();
                adt_def.variants[0]
                    .fields
                    .iter()
                    .map(|f| self.encode_snap_arg(
                        self.encoder.encode_struct_field(
                            &f.ident.to_string(),
                            f.ty(tcx, subst)
                            ),
                        self.encoder.encode_value_type(f.ty(tcx, subst)), // TODO
                        )
                    ).collect()
            },
            ty::TypeVariants::TyInt(_)
            | ty::TypeVariants::TyUint(_)
            | ty::TypeVariants::TyChar
            | ty::TypeVariants::TyBool => {
                vec![self.encode_snap_arg_local(SNAPSHOT_ARG)]
            },

            ty::TypeVariants::TyTuple(elems) => {
                let mut args = vec![];
                for (field_num, field_ty) in elems.iter().enumerate() {
                    let field_name = format!("tuple_{}", field_num);
                    let field = self.encoder.encode_raw_ref_field(field_name, field_ty);
                    let field_type = self.encoder.encode_value_type(field_ty);
                    args.push(
                        self.encode_snap_arg(field, field_type)
                    );
                }
                args
            }

            _ => unreachable!(),
        }
    }

    fn encode_snap_arg(&self, field: vir::Field, snap_type: vir::Type) -> vir::Expr {
        let field_type = field.typ.clone();
        match field.typ.clone() {
            vir::Type::TypedRef(name) => vir::Expr::FuncApp(
                self.encoder.encode_get_snapshot_func_name(name.clone()),
                vec![vir::Expr::Field(
                    Box::new(self.encode_snap_arg_local(SNAPSHOT_ARG)),
                    field,
                    vir::Position::default()
                )],
                vec![vir::LocalVar::new("self", field_type)],
                snap_type,
                vir::Position::default(),
            ),
            Type::Int | Type::Bool | Type::Domain(_) => { unreachable!() }
        }
    }

    pub fn encode_equals_func_ref(&self) -> vir::Function {
        let arg_type = vir::Type::TypedRef(get_ref_predicate_name(&self.predicate_name));
        let formal_left = vir::LocalVar::new(SNAPSHOT_LEFT, arg_type.clone());
        let formal_right = vir::LocalVar::new(SNAPSHOT_RIGHT, arg_type.clone());
        let arg_left = self.get_ref_field(formal_left.clone());
        let arg_right = self.get_ref_field(formal_right.clone());

        vir::Function {
            name: SNAPSHOT_EQUALS.to_string(),
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
                vir::BinOpKind::EqCmp,
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
        let arg = self.get_ref_field(self.encode_snap_arg_var(name.clone()));
        self.encode_snapshot_call(name, arg)
    }
}
