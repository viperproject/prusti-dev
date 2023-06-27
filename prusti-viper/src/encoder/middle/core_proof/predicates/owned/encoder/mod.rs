use super::PredicatesOwnedState;
use crate::encoder::middle::core_proof::lowerer::Lowerer;

mod predicate;
mod function;
mod function_range;

macro guard {
    ($self:ident, $set:ident, $ty:ident) => {
        let ty_identifier = vir_crate::common::identifier::WithIdentifier::get_identifier($ty);
        if $self.state().$set.contains(&ty_identifier) {
            return Ok(());
        }
        $self.state().$set.insert(ty_identifier);
    },
    (assert $self:ident, $set:ident, $ty:ident) => {
        let ty_identifier = vir_crate::common::identifier::WithIdentifier::get_identifier($ty);
        assert!(!$self.state().$set.contains(&ty_identifier));
        $self.state().$set.insert(ty_identifier);
    },
}

impl<'p, 'v: 'p, 'tcx: 'v> Lowerer<'p, 'v, 'tcx> {
    fn state(&mut self) -> &mut PredicatesOwnedState {
        &mut self.predicates_encoding_state.owned
    }
}
