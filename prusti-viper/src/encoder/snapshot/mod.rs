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
    let return_type: Type = match field_type.clone() {
        vir::Type::TypedRef(ref name) => vir::Type::Domain(name.clone()),
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

pub fn encode_valid_function(domain_name: String) -> vir::DomainFunc {
    let self_arg = vir::LocalVar {name: "self".to_string(), typ: vir::Type::Domain(domain_name.clone())};
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
