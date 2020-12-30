

use log::info;
use prusti_common::vir;

pub use self::purifier::ExprPurifier;

use super::errors::PositionlessEncodingResult;

mod purifier;



pub fn encode_field_domain_func(
    field_type: vir::Type,
    field_name: String,
    domain_name: String,
) -> vir::DomainFunc {

    let return_type: vir::Type = match field_type.clone() {
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