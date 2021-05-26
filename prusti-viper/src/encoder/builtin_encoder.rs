// © 2019, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use prusti_common::{vir, vir_local, vir::WithIdentifier};

const PRIMITIVE_VALID_DOMAIN_NAME: &str = "PrimitiveValidDomain";

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
    /// array lookup pure function, e.g. Array$4$u32$lookup_pure
    ArrayLookupPure {
        array_ty_pred: String,
        elem_ty_pred: String,
        array_len: usize,
        return_ty: vir::Type,
    },
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
            formal_returns: vec![vir_local!{ ret: {return_type} }],
        }
    }

    pub fn encode_builtin_function_name(&self, function: &BuiltinFunctionKind) -> String {
        match function {
            BuiltinFunctionKind::Unreachable(vir::Type::Int) => "builtin$unreach_int".to_string(),
            BuiltinFunctionKind::Unreachable(vir::Type::Bool) => "builtin$unreach_bool".to_string(),
            BuiltinFunctionKind::Unreachable(vir::Type::TypedRef(_)) => {
                "builtin$unreach_ref".to_string()
            }
            BuiltinFunctionKind::Unreachable(vir::Type::Domain(_)) => {
                "builtin$unreach_domain".to_string()
            }
            BuiltinFunctionKind::Unreachable(vir::Type::Snapshot(_)) => {
                "builtin$unreach_snap".to_string()
            }
            BuiltinFunctionKind::Undefined(vir::Type::Int) => "builtin$undef_int".to_string(),
            BuiltinFunctionKind::Undefined(vir::Type::Bool) => "builtin$undef_bool".to_string(),
            BuiltinFunctionKind::Undefined(vir::Type::TypedRef(_)) => "builtin$undef_ref".to_string(),
            // TODO: do Domain and Snapshot make sense here?
            BuiltinFunctionKind::Undefined(vir::Type::Domain(_)) => "builtin$undef_doman".to_string(),
            BuiltinFunctionKind::Undefined(vir::Type::Snapshot(_)) => "builtin$undef_snap".to_string(),
            BuiltinFunctionKind::ArrayLookupPure { elem_ty_pred, array_len, .. } => {
                format!("Array${}${}$lookup_pure", array_len, elem_ty_pred)
            }
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
            BuiltinFunctionKind::ArrayLookupPure { array_ty_pred, array_len, return_ty, .. } => {
                let self_var = vir_local!{ self: {vir::Type::TypedRef(array_ty_pred.clone())} };
                let idx_var = vir_local!{ idx: Int };

                vir::Function {
                    name: fn_name,
                    formal_args: vec![
                        // self,
                        self_var.clone(),
                        // idx,
                        idx_var.clone(),
                    ],
                    return_type: return_ty,
                    pres: vec![
                        // idx < {len}
                        vir!([vir::Expr::local(idx_var)]  < [vir::Expr::from(array_len)]),
                        // acc(self, read$())
                        vir::Expr::predicate_access_predicate(
                            array_ty_pred,
                            vir::Expr::local(self_var),
                            vir::PermAmount::Read,
                        )
                    ],
                    posts: vec![],
                    body: None,
                }
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
        let nat_domain_name = "NatDomain";
        // snapshot::NAT_DOMAIN_NAME;
        let zero = vir::DomainFunc {
            name: "zero".to_owned(),
            formal_args: vec![],
            return_type: vir::Type::Domain(nat_domain_name.to_owned()),
            unique: false,
            domain_name: nat_domain_name.to_owned(),
        };

        let functions = vec![zero]; // , snapshot::get_succ_func()];

        vir::Domain {
            name: nat_domain_name.to_owned(),
            functions,
            axioms: vec![],
            type_vars: vec![],
        }
    }

    fn encode_primitive_builtin_domain(&self) -> vir::Domain {
        //FIXME this does not check or handle the different sizes of primitve types
        let domain_name = PRIMITIVE_VALID_DOMAIN_NAME;

        let mut functions = vec![];
        let mut axioms = vec![];

        for t in &[vir::Type::Bool, vir::Type::Int] {
            //let f = snapshot::valid_func_for_type(t);
            let f = {
                let domain_name: String = match t {
                    // vir::Type::Domain(name) => name.clone(),
                    vir::Type::Bool | vir::Type::Int => domain_name.to_string(),
                    // vir::Type::TypedRef(_) => unreachable!(),
                    // vir::Type::Snapshot(_) => unreachable!(),
                    _ => unreachable!(),
                };

                let arg_typ: vir::Type = match t {
                    // vir::Type::Domain(name) => vir::Type::Domain(domain_name.clone()),
                    vir::Type::Bool => vir::Type::Bool,
                    vir::Type::Int => vir::Type::Int,
                    // vir::Type::TypedRef(_) => unreachable!(),
                    // vir::Type::Snapshot(_) => unreachable!(),
                    _ => unreachable!(),
                };

                let self_arg = vir::LocalVar {
                    name: "self".to_string(),
                    typ: arg_typ,
                };
                let df = vir::DomainFunc {
                    name: format!("{}$valid", domain_name),
                    formal_args: vec![self_arg],
                    return_type: vir::Type::Bool,
                    unique: false,
                    domain_name,
                };

                df
            };
            functions.push(f.clone());

            let forall_arg = vir_local!{ self: {t.clone()} };
            let function_app =
                vir::Expr::domain_func_app(f.clone(), vec![vir::Expr::local(forall_arg.clone())]);
            let body = vir::Expr::forall(
                vec![forall_arg],
                vec![vir::Trigger::new(vec![function_app.clone()])],
                function_app);
            let axiom = vir::DomainAxiom {
                name: format!("{}$axiom", f.get_identifier()),
                expr: body,
                domain_name: domain_name.to_string(),
            };
            axioms.push(axiom);
        }

        vir::Domain {
            name: domain_name.to_owned(),
            functions,
            axioms,
            type_vars: vec![],
        }
    }
}
