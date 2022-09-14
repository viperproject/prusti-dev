use crate::encoder::{
    errors::SpannedEncodingResult,
    middle::core_proof::transformations::symbolic_execution::egg::EGraphState,
};
use std::hash::{Hash, Hasher};
use vir_crate::low::{self as vir_low, operations::ty::Typed};

pub(super) fn arguments_match(
    args1: &[vir_low::Expression],
    args2: &[vir_low::Expression],
    solver: &EGraphState,
) -> SpannedEncodingResult<bool> {
    for (arg1, arg2) in args1.iter().zip(args2) {
        if !solver.is_equal(arg1, arg2)? {
            return Ok(false);
        }
    }
    Ok(true)
}

pub(in super::super) fn all_heap_independent(arguments: &[vir_low::Expression]) -> bool {
    arguments
        .iter()
        .all(|argument| argument.is_heap_independent())
}

pub(super) fn calculate_hash<T: Hash>(t: &T) -> u64 {
    let mut s = std::collections::hash_map::DefaultHasher::new();
    t.hash(&mut s);
    s.finish()
}

pub(super) fn is_place_non_aliased(place: &vir_low::Expression) -> bool {
    assert_eq!(place.get_type(), &vir_low::macros::ty!(PlaceOption));
    match place {
        vir_low::Expression::DomainFuncApp(domain_func_app)
            if domain_func_app.arguments.len() == 1 =>
        {
            let argument = &domain_func_app.arguments[0];
            if domain_func_app.function_name == "place_option_some" {
                true
            } else {
                is_place_non_aliased(argument)
            }
        }
        vir_low::Expression::DomainFuncApp(domain_func_app) => {
            assert_eq!(domain_func_app.function_name, "place_option_none");
            false
        }
        vir_low::Expression::LabelledOld(labelled_old) => is_place_non_aliased(&labelled_old.base),
        _ => unreachable!("place: {place}"),
    }
}
