use std::collections::HashMap;

use log::info;
use prusti_common::vir;

pub use self::purifier::ExprPurifier;

use super::{errors::PositionlessEncodingResult, snapshot_encoder::Snapshot};
use vir::Type;

mod purifier;

pub fn encode_field_domain_func(
    field_type: vir::Type,
    field_name: String,
    domain_name: String,
) -> vir::DomainFunc {
    let return_type: Type = match field_type {
        vir::Type::TypedRef(name) => vir::Type::Domain(name),
        t => t,
    };

    vir::DomainFunc {
        name: format!("{}$field${}", domain_name, field_name), //TODO get the right name
        formal_args: vec![vir::LocalVar {
            name: "self".to_string(),
            typ: vir::Type::Domain(domain_name.to_string()),
        }],
        return_type,
        unique: false,
        domain_name: domain_name.to_string(),
    }
}


/// Returns the T$valid function for the given type
pub fn valid_func_for_type(typ : &vir::Type) -> vir::DomainFunc {
    let domain_name : String = match typ {
        Type::Domain(name) => name.clone(),
        Type::Bool | Type::Int => "PrimitiveValidDomain".to_string(),
        Type::TypedRef(_) => unreachable!()
    };

    let arg_typ: Type = match typ {
        Type::Domain(name)  =>  vir::Type::Domain(domain_name.clone()),
        Type::Bool => Type::Bool,
        Type::Int => Type::Int,
        Type::TypedRef(_) => unreachable!()
    };


    let self_arg = vir::LocalVar {name: "self".to_string(), typ: arg_typ};
    let df = vir::DomainFunc {
        name: format!("{}$valid", domain_name),
        formal_args: vec![self_arg],
        return_type: vir::Type::Bool,
        unique: false,
        domain_name,
    };

    df
}


pub fn transalte_type(t: Type, snapshots: &HashMap<String, Box<Snapshot>>,) -> Type {
    match t {
        Type::TypedRef(name) => match name.as_str() {
            "i32" => Type::Int,
            "bool" => Type::Bool,
            _ => {
                let domain_name = snapshots
                    .get(&name)
                    .and_then(|snap| snap.domain())
                    .map(|domain| domain.name)
                    .expect(&format!("No matching domain for '{}'", name));

                vir::Type::Domain(domain_name)
            }
        },
        o @ _ => o,
    }
}
