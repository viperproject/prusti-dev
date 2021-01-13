use std::collections::HashMap;

use log::{warn,info};
use prusti_common::vir;

pub use self::purifier::ExprPurifier;

use super::{errors::EncodingResult, snapshot_encoder::Snapshot};
use vir::Type;

mod purifier;


pub const NAT_DOMAIN_NAME: &str = "$Nat$";

pub fn encode_field_domain_func(
    field_type: vir::Type,
    field_name: String,
    domain_name: String,
    variant_name: Option<String>
) -> vir::DomainFunc {
    let mut field_domain_name = domain_name.clone();
    if let Some(s) = variant_name {
        field_domain_name += &s;
    }
    let return_type: Type = match field_type {
        vir::Type::TypedRef(name) => vir::Type::Domain(name),
        t => t,
    };

    vir::DomainFunc {
        name: format!("{}$field${}", field_domain_name, field_name), //TODO get the right name
        formal_args: vec![vir::LocalVar {
            name: "self".to_string(),
            typ: vir::Type::Domain(domain_name.to_string()),
        }],
        return_type,
        unique: false,
        domain_name: domain_name.to_string(),
    }
}


pub fn encode_unfold_witness(domain_name: String) -> vir::DomainFunc {

    let self_type = Type::Domain(domain_name.clone());
    let self_arg = vir::LocalVar {name: "self".to_string(), typ: self_type};

    let nat_type = Type::Domain(NAT_DOMAIN_NAME.to_owned());
    let nat_arg = vir::LocalVar {name: "count".to_string(), typ: nat_type};

    vir::DomainFunc {
        name: format!("{}$UnfoldWitness", domain_name),
        formal_args: vec![self_arg, nat_arg],
        return_type: vir::Type::Bool,
        unique: false,
        domain_name,
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

fn unbox(name: String) -> String {
    let start = "m_alloc$$boxed$$Box$_beg_$";
    let end = "$_sep_$m_alloc$$alloc$$Global$_beg_$_end_$_end_";
    if !name.ends_with(end) {
        return name;
    }

    if !name.starts_with(start) {
        return name;
    }

    let remaining = name.len() - start.len() -end.len();

    return name.chars().skip(start.len()).take(remaining).collect();
}


pub fn translate_type(t: Type, snapshots: &HashMap<String, Box<Snapshot>>,) -> Type {
    warn!("translate_type t={:?} sn={:?}", t, snapshots.keys());
    match t {
        Type::TypedRef(name) => match name.as_str() {
            "i32" | "usize" | "u32" => Type::Int,
            "bool" => Type::Bool,
            _ => {
                let name = unbox(name);
                let domain_name = snapshots
                    .get(&name)
                    .and_then(|snap| snap.domain())
                    .map(|domain| domain.name)
                    .expect(&format!("No matching domain for '{}' in '{:?}'", name,snapshots));

                vir::Type::Domain(domain_name)
            }
        },
        o @ _ => o,
    }
}



#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn test_unbox() {
    let res = unbox("m_alloc$$boxed$$Box$_beg_$m_len_lookup$$List$_beg_$_end_$_sep_$m_alloc$$alloc$$Global$_beg_$_end_$_end_".to_string());
    assert_eq!(res, "m_len_lookup$$List$_beg_$_end_".to_string());

    assert_eq!(unbox("u32".to_string()), "u32".to_string());
    }

}