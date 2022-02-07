use super::super::super::ast;
use crate::common::identifier::WithIdentifier;

pub(super) fn append_type_arguments(identifier: &mut String, type_arguments: &[ast::ty::Type]) {
    identifier.push('$');
    assert!(!identifier.contains('<'), "identifier: {}", identifier);
    for arg in type_arguments {
        identifier.push_str(&arg.get_identifier());
        identifier.push('$');
        assert!(
            !identifier.contains('<'),
            "identifier: {}, arg: {:?}",
            identifier,
            arg
        );
    }
    assert!(!identifier.contains('<'), "identifier: {}", identifier);
}
