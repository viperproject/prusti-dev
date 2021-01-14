// © 2019, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use crate::encoder::snapshot;
use prusti_common::{vir, vir::WithIdentifier};

#[derive(Clone, Copy, Debug, Hash, Eq, PartialEq)]
pub enum BuiltinMethodKind {
    HavocBool,
    HavocInt,
    HavocRef,
}

#[derive(Clone, Debug, Hash, Eq, PartialEq)]
pub enum BuiltinFunctionKind {
    /// type
    Unreachable(vir::Type),
    /// type
    Undefined(vir::Type),
}
#[derive(Clone, Debug, Hash, Eq, PartialEq)]
pub enum BuiltinDomainKind {
    Nat,
    Primitive,
}

pub struct BuiltinEncoder {}

impl BuiltinEncoder {
    pub fn new() -> Self {
        Self {}
    }

    pub fn encode_builtin_method_name(&self, method: BuiltinMethodKind) -> String {
        match method {
            BuiltinMethodKind::HavocBool => "builtin$havoc_bool".to_string(),
            BuiltinMethodKind::HavocInt => "builtin$havoc_int".to_string(),
            BuiltinMethodKind::HavocRef => "builtin$havoc_ref".to_string(),
        }
    }

    pub fn encode_builtin_method_def(&self, method: BuiltinMethodKind) -> vir::BodylessMethod {
        let return_type = match method {
            BuiltinMethodKind::HavocBool => vir::Type::Bool,
            BuiltinMethodKind::HavocInt => vir::Type::Int,
            BuiltinMethodKind::HavocRef => vir::Type::TypedRef("".to_string()),
        };
        vir::BodylessMethod {
            name: self.encode_builtin_method_name(method),
            formal_args: vec![],
            formal_returns: vec![vir::LocalVar::new("ret", return_type)],
        }
    }

    pub fn encode_builtin_function_name(&self, function: &BuiltinFunctionKind) -> String {
        match function {
            BuiltinFunctionKind::Unreachable(vir::Type::Int) => format!("builtin$unreach_int"),
            BuiltinFunctionKind::Unreachable(vir::Type::Bool) => format!("builtin$unreach_bool"),
            BuiltinFunctionKind::Unreachable(vir::Type::TypedRef(_)) => {
                format!("builtin$unreach_ref")
            }
            BuiltinFunctionKind::Unreachable(vir::Type::Domain(_)) => {
                format!("builtin$unreach_domain")
            }
            BuiltinFunctionKind::Undefined(vir::Type::Int) => format!("builtin$undef_int"),
            BuiltinFunctionKind::Undefined(vir::Type::Bool) => format!("builtin$undef_bool"),
            BuiltinFunctionKind::Undefined(vir::Type::TypedRef(_)) => format!("builtin$undef_ref"),
            BuiltinFunctionKind::Undefined(vir::Type::Domain(_)) => format!("builtin$undef_doman"),
        }
    }

    pub fn encode_builtin_function_def(&self, function: BuiltinFunctionKind) -> vir::Function {
        let fn_name = self.encode_builtin_function_name(&function);
        match function {
            BuiltinFunctionKind::Unreachable(typ) => vir::Function {
                name: fn_name,
                formal_args: vec![],
                return_type: typ,
                // Precondition is false, because we want to be sure that this function is never used
                pres: vec![false.into()],
                posts: vec![],
                body: None,
            },
            BuiltinFunctionKind::Undefined(typ) => vir::Function {
                name: fn_name,
                formal_args: vec![],
                return_type: typ,
                pres: vec![],
                posts: vec![],
                body: None,
            },
        }
    }

    pub fn encode_builtin_domain(&self, kind: BuiltinDomainKind) -> vir::Domain {
        match kind {
            BuiltinDomainKind::Nat => self.encode_nat_builtin_domain(),
            BuiltinDomainKind::Primitive => self.encode_primitive_builtin_domain(),
        }
    }

    fn encode_nat_builtin_domain(&self) -> vir::Domain {
        let nat_domain_name = snapshot::NAT_DOMAIN_NAME;
        let zero = vir::DomainFunc {
            name: "zero".to_owned(),
            formal_args: vec![],
            return_type: vir::Type::Domain(nat_domain_name.to_owned()),
            unique: false,
            domain_name: nat_domain_name.to_owned(),
        };

        let functions = vec![zero, snapshot::get_succ_func()];

        vir::Domain {
            name: nat_domain_name.to_owned(),
            functions,
            axioms: vec![],
            type_vars: vec![],
        }
    }

    fn encode_primitive_builtin_domain(&self) -> vir::Domain {
        //FIXME this does not check or handel the different sizes of primitve types
        let domain_name = "PrimitiveValidDomain";

        let mut functions = vec![];
        let mut axioms = vec![];
        for t in &[vir::Type::Bool, vir::Type::Int] {
            let f = snapshot::valid_func_for_type(t);
            functions.push(f.clone());

            let forall_arg = vir::LocalVar {
                name: "self".to_owned(),
                typ: t.clone(),
            };
            let function_app =
                vir::Expr::domain_func_app(f.clone(), vec![vir::Expr::local(forall_arg.clone())]);
            let body = vir::Expr::and(function_app, true.into());
            let e = vir::Expr::forall(vec![forall_arg], vec![], body); //TODO triggers
            let ax = vir::DomainAxiom {
                name: format!("{}$axiom", f.get_identifier()),
                expr: e,
                domain_name: domain_name.to_string(),
            };
            axioms.push(ax); //TODO
        }

        vir::Domain {
            name: domain_name.to_owned(),
            functions,
            axioms,
            type_vars: vec![],
        }
    }
}
