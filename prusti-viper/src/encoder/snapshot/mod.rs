

use log::info;
use prusti_common::vir;

pub use self::purifier::ExprPurifier;

use super::errors::PositionlessEncodingResult;

mod purifier;



pub fn encode_field_domain_func_from_snapshot(
    field_type: vir::Type,
    field_name: String,
    domain_name: String,
) -> PositionlessEncodingResult<vir::DomainFunc> {
    info!(
        "encode_field_domain_func_from_snapshot field_type={} field_name={} domain_name={}",
        field_type, field_name, domain_name
    );
    //let return_type_name : String = snapshot.domain().map(|e|e.name.clone()).unwrap();

    let return_type: vir::Type = match field_type.clone() {
        vir::Type::TypedRef(ref name) => vir::Type::Domain(name.clone()),
        t => t,
    };

    //let return_type = vir::Type::Domain(return_type_name);

    Ok(vir::DomainFunc {
        name: format!("{}$field${}", domain_name, field_name), //TODO get the right name
        formal_args: vec![vir::LocalVar {
            name: "self".to_string(),
            typ: vir::Type::Domain(domain_name.to_string()),
        }],
        return_type,
        unique: false,
        domain_name: domain_name.to_string(),
    })
}