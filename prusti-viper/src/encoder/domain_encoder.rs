// © 2020, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use encoder::vir;
use encoder::Encoder;
use rustc::ty;
use encoder::vir::{PermAmount, Type};


const SNAPSHOT_DOMAIN_SUFFIX: &str = "$Snap";
const SNAPSHOT_CONS: &str = "cons$";
const SNAPSHOT_GET: &str = "get_snap$";
const SNAPSHOT_ARG: &str = "_arg";

pub struct DomainEncoder<'p, 'v: 'p, 'r: 'v, 'a: 'r, 'tcx: 'a> {
    encoder: &'p Encoder<'v, 'r, 'a, 'tcx>,
    ty: ty::Ty<'tcx>, // TODO this is the type we are talking about
    domain_name: String,
}

impl<'p, 'v, 'r: 'v, 'a: 'r, 'tcx: 'a> DomainEncoder<'p, 'v, 'r, 'a, 'tcx> {
    pub fn new(encoder: &'p Encoder<'v, 'r, 'a, 'tcx>, ty: ty::Ty<'tcx>) -> Self {
        let domain_name = format!(
            "{}{}",
            encoder.encode_type_predicate_use(ty).clone(),
            SNAPSHOT_DOMAIN_SUFFIX
        );
        DomainEncoder { encoder, ty, domain_name }
    }

    pub fn encode_domain_name(&self) -> String {
        self.domain_name.clone()
    }

    pub fn encode_snap_domain_def(&self) -> vir::Domain {
        vir::Domain {
            name: self.encode_domain_name(),
            functions: self.encode_snap_functions(),
            axioms: self.encode_snap_axioms(),
            type_vars: vec![]
        }
    }

    fn encode_snap_functions(&self) -> Vec<vir::DomainFunction> {
        let cons_fun = vir::DomainFunction {
            name: SNAPSHOT_CONS.to_string(),
            formal_args: self.encode_snap_formal_args(),
            return_type: vir::Type::Domain(self.domain_name.clone()),
            unique: false,
            domain_name: self.domain_name.clone(),
        };
        vec![cons_fun]
    }

    fn encode_snap_formal_args(&self) -> Vec<vir::LocalVar> {
        let mut counter = 0;
        let mut formal_args = vec![];
        match self.ty.sty {
            ty::TypeVariants::TyAdt(adt_def, subst) if !adt_def.is_box() => {
                assert!(adt_def.variants.len() == 1);
                let tcx = self.encoder.env().tcx();
                for field in &adt_def.variants[0].fields {
                    let field_type = &self.encoder.encode_value_type(field.ty(tcx, subst));
                    formal_args.push(
                        self.encode_local_var(counter, field_type)
                    );
                    counter += 1
                }
            },
            _ => unreachable!(),
        }
        formal_args
    }

    fn encode_local_var(&self, counter: i32, field_type: &vir::Type) -> vir::LocalVar {
        let typ = match field_type.clone() {
            vir::Type::TypedRef(ref name) => {
                println!("{}", name);
                vir::Type::Domain(name.clone())
            },
            t => t,
        };
        let name = format!("arg${}", counter);
        vir::LocalVar { name, typ }
    }

    fn encode_snap_axioms(&self) -> Vec<vir::DomainAxiom> {
        vec![] // TODO
    }

    pub fn encode_snap_compute_def(&self) -> vir::Function {
        let predicate_name = self.encoder.encode_type_predicate_use(self.ty);
        let arg_var = self.encode_snap_arg_var();
        let return_type = vir::Type::Domain(self.domain_name.clone());
        vir::Function {
            name: SNAPSHOT_GET.to_string(),
            formal_args: vec![arg_var.clone()],
            return_type: return_type.clone(),
            pres: vec![vir::Expr::PredicateAccessPredicate(
                predicate_name.clone(),
                Box::new(vir::Expr::Local(arg_var, vir::Position::default())),
                PermAmount::Write,
                vir::Position::default())],
            posts: vec![],
            body: Some(vir::Expr::Unfolding(
                predicate_name,
                vec![vir::Expr::Local(self.encode_snap_arg_var(), vir::Position::default())],
                Box::new(vir::Expr::FuncApp(
                    SNAPSHOT_CONS.to_string(),
                    self.encode_snap_args(),
                    self.encode_snap_formal_args(),
                    return_type,
                    vir::Position::default(),
                )),
                vir::PermAmount::Write,
                None,
                vir::Position::default(),
            )),
        }
    }

    fn encode_snap_arg_var(&self) -> vir::LocalVar {
        let predicate_name = self.encoder.encode_type_predicate_use(self.ty);
        let typ = vir::Type::TypedRef(predicate_name.clone());
        let arg_name = SNAPSHOT_ARG.to_string();
        vir::LocalVar { name: arg_name, typ }
    }

    fn encode_snap_args(&self) -> Vec<vir::Expr> {
        match self.ty.sty {
            ty::TypeVariants::TyAdt(adt_def, subst) if !adt_def.is_box() => {
                assert!(adt_def.variants.len() == 1);
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
                            self.encode_snap_arg_var(),
                            vir::Position::default()
                        )
                    ), field, vir::Position::default()
                )],
                vec![vir::LocalVar::new("self", field_type)],
                self.encoder.encode_get_domain_type(name.clone()),
                vir::Position::default(),
            ),
            Type::Int => { unimplemented!() } // TODO
            Type::Bool => { unimplemented!() }
            Type::Domain(_) => unreachable!(),
        }
    }
}
