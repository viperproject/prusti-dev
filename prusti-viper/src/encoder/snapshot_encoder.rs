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
        vir::Expr::DomainFuncApp(cons_function, args, vir::Position::default())
    }
}

pub struct Snapshot {
    pub predicate_name: String,
    pub snap_func: vir::Function,
    pub snap_domain: Option<SnapshotDomain>, // for non-primitive types we need a new snapshot domain
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
            Some(s) => (format!("ref${}", self.predicate_name.clone()), s.equals_func_ref.clone()),
            None => unreachable!()
        }
    }
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
            ty::TypeVariants::TyAdt(adt_def, _) if !adt_def.is_box() => {
                // TODO CMFIXME
                if adt_def.variants.len() != 1 {
                    warn!("Generating equality tests for enums is not supported yet");
                }
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

    fn encode_snap_func_primitive(&self, field: vir::Field) -> vir:: Function {
        let return_type = self.encoder.encode_value_type(self.ty);
        let body = vir::Expr::Field(
            Box::new(
                vir::Expr::Local(
                    self.encode_snap_arg_var(SNAPSHOT_ARG),
                    vir::Position::default()
                )
            ),
            field,
            vir::Position::default()
        );
        self.encode_snap_func(return_type, body)
    }

    fn encode_snap_func(&self, return_type: vir::Type, body: vir::Expr) -> vir::Function {
        vir::Function {
            name: SNAPSHOT_GET.to_string(), //format!("{}${}", SNAPSHOT_GET, self.predicate_name),
            formal_args: vec![self.encode_snap_arg_var(SNAPSHOT_ARG)],
            return_type: return_type.clone(),
            pres: vec![self.encode_snap_predicate_access(SNAPSHOT_ARG.clone())],
            posts: vec![],
            body: Some(vir::Expr::Unfolding(
                self.predicate_name.clone(),
                vec![vir::Expr::Local(
                    self.encode_snap_arg_var(SNAPSHOT_ARG),
                    vir::Position::default()
                )],
                Box::new(body),
                vir::PermAmount::Read,
                None,
                vir::Position::default(),
            )),
        }
    }

    fn encode_snap_predicate_access<S: Into<String>>(&self, arg_name: S) -> vir::Expr {
        vir::Expr::PredicateAccessPredicate(
            self.predicate_name.clone(),
            Box::new(vir::Expr::Local(
                self.encode_snap_arg_var(arg_name),
                vir::Position::default()
            )),
            PermAmount::Read,
            vir::Position::default())
    }

    fn encode_snap_arg_var<S: Into<String>>(&self, arg_name: S) -> vir::LocalVar {
        vir::LocalVar::new(arg_name, self.get_predicate_type())
    }

    fn get_predicate_type(&self) -> vir::Type {
        vir::Type::TypedRef(self.predicate_name.clone())
    }

    fn encode_snap_struct(&self) -> Snapshot {
        let snap_domain = SnapshotDomain{
            domain: self.encode_domain_struct(),
            equals_func: self.encode_equals_func_struct(),
            equals_func_ref: self.encode_equals_func_struct_ref(),
        };

        Snapshot {
            predicate_name: self.predicate_name.clone(),
            snap_func: self.encode_snap_func(
                snap_domain.get_type(),
                snap_domain.call_snap_func(
                    self.encode_snap_func_struct_args()
                )
            ),
            snap_domain: Some(snap_domain),
        }
    }

    fn encode_domain_struct(&self) -> vir::Domain {
        vir::Domain {
            name: self.encode_domain_name(),
            functions: self.encode_domain_struct_cons(),
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

    fn encode_domain_struct_cons(&self) -> Vec<vir::DomainFunc> {
        let domain_name = self.encode_domain_name();
        let cons_fun = vir::DomainFunc {
            name: SNAPSHOT_CONS.to_string(),
            formal_args: self.encode_domain_struct_cons_formal_args(),
            return_type: vir::Type::Domain(domain_name.clone()),
            unique: false,
            domain_name,
        };
        vec![cons_fun]
    }
    pub fn encode_equals_func_struct(&self) -> vir::Function {
        let left = "_left";
        let right = "_right";
        vir::Function {
            name: SNAPSHOT_EQUALS.to_string(),
            formal_args: vec![
                self.encode_snap_arg_var(left),
                self.encode_snap_arg_var(right),
            ],
            return_type: vir::Type::Bool,
            pres: vec![
                self.encode_snap_predicate_access(left),
                self.encode_snap_predicate_access(right),
            ],
            posts: vec![],
            body: Some(vir::Expr::BinOp(
                vir::BinOpKind::EqCmp,
                Box::new(self.encode_snapshot_call(left)),
                Box::new(self.encode_snapshot_call(right)),
                vir::Position::default(),
            )),
        }
    }

    fn encode_snapshot_call<S: Into<String>>(&self, arg_name: S) -> vir::Expr {
        let name = arg_name.into();
        vir::Expr::FuncApp(
            SNAPSHOT_GET.to_string(),
            vec![vir::Expr::Local(self.encode_snap_arg_var(name.clone()), vir::Position::default())],
            vec![self.encode_snap_arg_var(name)],
            vir::Type::Domain(self.encode_domain_name()),
            vir::Position::default(),
        )
    }

    fn encode_domain_struct_cons_formal_args(&self) -> Vec<vir::LocalVar> {
        let mut counter = 0;
        let mut formal_args = vec![];
        match self.ty.sty {
            ty::TypeVariants::TyAdt(adt_def, subst) if !adt_def.is_box() => {
                // TODO fo far this is for structs only
                let tcx = self.encoder.env().tcx();
                for field in &adt_def.variants[0].fields {
                    self.encoder.encode_snapshot(field.ty(tcx, subst)); // CMFIXME
                    let field_type = &self.encoder.encode_value_type(field.ty(tcx, subst));
                    formal_args.push(
                        self.encode_local_var(counter, field_type)
                    );
                    counter += 1
                }
            },
            ty::TypeVariants::TyInt(_) => {
                formal_args.push(self.encode_snap_arg_var(SNAPSHOT_ARG))
            },
            _ => unreachable!(),
        }
        formal_args
    }

    fn encode_local_var(&self, counter: i32, field_type: &vir::Type) -> vir::LocalVar {
        let typ = match field_type.clone() {
            vir::Type::TypedRef(ref name) => {
                vir::Type::Domain(name.clone())
            },
            t => t,
        };
        let name = format!("arg${}", counter);
        vir::LocalVar { name, typ }
    }

    fn encode_snap_func_struct_args(&self) -> Vec<vir::Expr> {
        match self.ty.sty {
            ty::TypeVariants::TyAdt(adt_def, subst) if !adt_def.is_box() => {
                // TODO CMFIXME so far this works only for structs
                let tcx = self.encoder.env().tcx();
                adt_def.variants[0]
                    .fields
                    .iter()
                    .map(|f| self.encode_snap_arg(
                        self.encoder.encode_struct_field(
                            &f.ident.to_string(),
                            f.ty(tcx, subst)
                            )
                        )
                    ).collect()
            },
            ty::TypeVariants::TyInt(_) => {
                vec![vir::Expr::Local(
                    self.encode_snap_arg_var(SNAPSHOT_ARG),
                    vir::Position::default()
                )]
            },
            _ => unreachable!(),
        }
    }

    fn encode_snap_arg(&self, field: vir::Field) -> vir::Expr {
        let field_type = field.typ.clone();
        match field.typ.clone() {
            vir::Type::TypedRef(name) => vir::Expr::FuncApp(
                self.encoder.encode_get_snapshot_func_name(name.clone()),
                vec![vir::Expr::Field(
                    Box::new(
                        vir::Expr::Local(
                            self.encode_snap_arg_var(SNAPSHOT_ARG),
                            vir::Position::default()
                        )
                    ), field, vir::Position::default()
                )],
                vec![vir::LocalVar::new("self", field_type)],
                self.encode_type_name(name.clone()),
                vir::Position::default(),
            ),
            Type::Int | Type::Bool | Type::Domain(_) => { unimplemented!() }
        }
    }

    // TODO CMFIXME
    fn encode_type_name(&self, name: String) -> vir::Type {
        if name == "i32" { // TODO
            vir::Type::Int
        } else {
            match &self.encoder.encode_get_domain_type(name) {
                Some(typ) => typ.clone(),
                None => unreachable!(),
            }
        }
    }

    // TODO CMFIXME unify with encode_equals_def
    pub fn encode_equals_func_struct_ref(&self) -> vir::Function {

        let ref_predicate_name = format!("ref${}", self.predicate_name.clone());
        let arg_type = vir::Type::TypedRef(ref_predicate_name.clone());

        let formal_arg_left = vir::LocalVar::new("_left".to_string(), arg_type.clone());
        let formal_arg_right = vir::LocalVar::new("_right".to_string(), arg_type.clone());

        let arg_left = vir::Expr::Field(
            Box::new(vir::Expr::Local(formal_arg_left.clone(), vir::Position::default())),
            vir::Field::new("val_ref", self.get_predicate_type()),
            vir::Position::default()
        );

        let arg_right = vir::Expr::Field(
            Box::new(vir::Expr::Local(formal_arg_right.clone(), vir::Position::default())),
            vir::Field::new("val_ref", self.get_predicate_type()),
            vir::Position::default()
        );

        let call_arg_left = vir::LocalVar::new("_left".to_string(), self.get_predicate_type());
        let call_arg_right = vir::LocalVar::new("_right".to_string(), self.get_predicate_type());

        vir::Function {
            name: SNAPSHOT_EQUALS.to_string(),
            formal_args: vec![formal_arg_left.clone(), formal_arg_right.clone()],
            return_type: vir::Type::Bool,
            pres: vec![
                vir::Expr::FieldAccessPredicate(
                    Box::new(arg_left.clone()),
                    PermAmount::Read,
                    vir::Position::default()
                ),
                vir::Expr::PredicateAccessPredicate(
                    self.predicate_name.clone(),
                    Box::new(arg_left.clone()),
                    PermAmount::Read,
                    vir::Position::default()
                ),
                vir::Expr::FieldAccessPredicate(
                    Box::new(arg_right.clone()),
                    PermAmount::Read,
                    vir::Position::default()
                ),
                vir::Expr::PredicateAccessPredicate(
                    self.predicate_name.clone(),
                    Box::new(arg_right.clone()),
                    PermAmount::Read,
                    vir::Position::default()
                ),
            ],
            posts: vec![],
            body: Some(vir::Expr::BinOp(
                vir::BinOpKind::EqCmp,
                Box::new(self.encode_ref_snapshot_call(call_arg_left)),
                Box::new(self.encode_ref_snapshot_call(call_arg_right)),
                vir::Position::default(),
            )),
        }
    }

    // TODO CMFIXME
    fn encode_ref_snapshot_call(&self, formal_arg: vir::LocalVar) -> vir::Expr {
        let arg = vir::Expr::Field(
            Box::new(vir::Expr::Local(formal_arg.clone(), vir::Position::default())),
            vir::Field::new("val_ref", self.get_predicate_type()),
            vir::Position::default()
        );
        vir::Expr::FuncApp(
            SNAPSHOT_GET.to_string(),
            vec![arg],
            vec![formal_arg],
            vir::Type::Domain(self.encode_domain_name()),
            vir::Position::default(),
        )
    }


}
