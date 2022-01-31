use crate::encoder::{
    errors::SpannedEncodingResult,
    high::types::HighTypeEncoderInterface,
    middle::core_proof::{
        lowerer::{DomainsLowererInterface, Lowerer, VariablesLowererInterface},
        predicates_memory_block::PredicatesMemoryBlockInterface,
    },
};
use rustc_hash::FxHashSet;
use std::{borrow::Cow, collections::BTreeMap};
use vir_crate::{
    common::{
        expression::{BinaryOperationHelpers, ExpressionIterator, QuantifierHelpers},
        identifier::WithIdentifier,
    },
    low::{self as vir_low, operations::ToLow},
    middle::{self as vir_mid, operations::ty::Typed},
};

use super::IntoSnapshot;

#[derive(Default)]
pub(in super::super) struct SnapshotsState {
    /// The list of types for which `to_bytes` was encoded.
    encoded_to_bytes: FxHashSet<vir_mid::Type>,
    /// Mapping from variable names to their versions.
    snapshot_variable_versions: BTreeMap<String, u64>,
}

trait Private {
    fn encode_validity_axiom_name(&self, ty: &vir_mid::Type) -> SpannedEncodingResult<String>;
    fn insert_validity_axiom(
        &mut self,
        ty: &vir_mid::Type,
        body: vir_low::Expression,
    ) -> SpannedEncodingResult<()>;
    fn encode_snapshot_domain_type(
        &mut self,
        ty: &vir_mid::Type,
    ) -> SpannedEncodingResult<vir_low::Type>;
    fn insert_snapshot_axiom(
        &mut self,
        ty: &vir_mid::Type,
        axiom: vir_low::DomainAxiomDecl,
    ) -> SpannedEncodingResult<()>;
    fn encode_validity_axioms_with_fields<'a>(
        &mut self,
        ty: &vir_mid::Type,
        fields: impl Iterator<Item = Cow<'a, vir_mid::FieldDecl>>,
    ) -> SpannedEncodingResult<()>;
    fn snapshot_copy_except(
        &mut self,
        statements: &mut Vec<vir_low::Statement>,
        old_snapshot_root: vir_low::VariableDecl,
        new_snapshot_root: vir_low::VariableDecl,
        place: &vir_mid::Expression,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<(vir_low::Expression, vir_low::Expression)>;
    fn create_snapshot_variable(
        &mut self,
        variable: &vir_mid::VariableDecl,
        version: u64,
    ) -> SpannedEncodingResult<vir_low::VariableDecl>;
}

impl<'p, 'v: 'p, 'tcx: 'v> Private for Lowerer<'p, 'v, 'tcx> {
    fn encode_validity_axiom_name(&self, ty: &vir_mid::Type) -> SpannedEncodingResult<String> {
        Ok(format!("{}$validity_axiom", ty.get_identifier()))
    }
    fn insert_validity_axiom(
        &mut self,
        ty: &vir_mid::Type,
        body: vir_low::Expression,
    ) -> SpannedEncodingResult<()> {
        let axiom = vir_low::DomainAxiomDecl {
            name: self.encode_validity_axiom_name(ty)?,
            body,
        };
        self.insert_snapshot_axiom(ty, axiom)
    }
    fn encode_snapshot_domain_type(
        &mut self,
        ty: &vir_mid::Type,
    ) -> SpannedEncodingResult<vir_low::Type> {
        Ok(vir_low::Type::domain(self.encode_snapshot_domain_name(ty)?))
    }
    fn insert_snapshot_axiom(
        &mut self,
        ty: &vir_mid::Type,
        axiom: vir_low::DomainAxiomDecl,
    ) -> SpannedEncodingResult<()> {
        let domain_name = self.encode_snapshot_domain_name(ty)?;
        self.declare_axiom(&domain_name, axiom)
    }
    fn encode_validity_axioms_with_fields<'a>(
        &mut self,
        ty: &vir_mid::Type,
        fields: impl Iterator<Item = Cow<'a, vir_mid::FieldDecl>>,
    ) -> SpannedEncodingResult<()> {
        let snapshot_type = ty.create_snapshot(self)?;
        let snapshot = vir_low::VariableDecl::new("snapshot", snapshot_type);
        let snapshot_valid =
            self.encode_snapshot_validity_expression(snapshot.clone().into(), ty)?;
        let mut conjuncts = Vec::new();
        for field in fields {
            let field_snapshot = self.encode_field_snapshot(
                ty,
                &field,
                snapshot.clone().into(),
                Default::default(),
            )?;
            let field_snapshot_valid =
                self.encode_snapshot_validity_expression(field_snapshot.clone(), &field.ty)?;
            conjuncts.push(field_snapshot_valid);
        }
        let body = vir_low::Expression::forall(
            vec![snapshot],
            vec![vir_low::Trigger::new(vec![snapshot_valid.clone()])],
            vir_low::Expression::equals(snapshot_valid, conjuncts.into_iter().conjoin()),
        );
        self.insert_validity_axiom(ty, body)?;
        Ok(())
    }
    /// Copy all values of the old snapshot into the new snapshot, except the
    /// ones that belong to `place`.
    fn snapshot_copy_except(
        &mut self,
        statements: &mut Vec<vir_low::Statement>,
        old_snapshot_root: vir_low::VariableDecl,
        new_snapshot_root: vir_low::VariableDecl,
        place: &vir_mid::Expression,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<(vir_low::Expression, vir_low::Expression)> {
        use vir_low::macros::*;
        if let Some(parent) = place.get_parent_ref() {
            let (old_snapshot, new_snapshot) = self.snapshot_copy_except(
                statements,
                old_snapshot_root,
                new_snapshot_root,
                parent,
                position,
            )?;
            let parent_type = parent.get_type();
            let type_decl = self.encoder.get_type_decl_mid(parent_type)?;
            match &type_decl {
                vir_mid::TypeDecl::Bool
                | vir_mid::TypeDecl::Int(_)
                | vir_mid::TypeDecl::Float(_) => {
                    unreachable!("place: {}", place);
                }
                vir_mid::TypeDecl::TypeVar(_) => unimplemented!("ty: {}", type_decl),
                vir_mid::TypeDecl::Tuple(_) => unimplemented!("ty: {}", type_decl),
                vir_mid::TypeDecl::Struct(decl) => {
                    let place_field = place.clone().unwrap_field(); // FIXME: Implement a macro that takes a reference to avoid clonning.
                    for field in decl.iter_fields() {
                        if field.as_ref() != &place_field.field {
                            let old_field_snapshot = self.encode_field_snapshot(
                                parent_type,
                                &field,
                                old_snapshot.clone(),
                                Default::default(),
                            )?;
                            let new_field_snapshot = self.encode_field_snapshot(
                                parent_type,
                                &field,
                                new_snapshot.clone(),
                                Default::default(),
                            )?;
                            statements.push(
                                stmtp! { position => assume ([new_field_snapshot] == [old_field_snapshot])},
                            );
                        }
                    }
                    Ok((
                        self.encode_field_snapshot(
                            parent_type,
                            &place_field.field,
                            old_snapshot,
                            Default::default(),
                        )?,
                        self.encode_field_snapshot(
                            parent_type,
                            &place_field.field,
                            new_snapshot,
                            Default::default(),
                        )?,
                    ))
                }
                vir_mid::TypeDecl::Enum(_) => unimplemented!("ty: {}", type_decl),
                vir_mid::TypeDecl::Array(_) => unimplemented!("ty: {}", type_decl),
                vir_mid::TypeDecl::Reference(_) => unimplemented!("ty: {}", type_decl),
                vir_mid::TypeDecl::Never => unimplemented!("ty: {}", type_decl),
                vir_mid::TypeDecl::Closure(_) => unimplemented!("ty: {}", type_decl),
                vir_mid::TypeDecl::Unsupported(_) => unimplemented!("ty: {}", type_decl),
            }
        } else {
            // We reached the root. Nothing to do here.
            Ok((old_snapshot_root.into(), new_snapshot_root.into()))
        }
    }
    fn create_snapshot_variable(
        &mut self,
        variable: &vir_mid::VariableDecl,
        version: u64,
    ) -> SpannedEncodingResult<vir_low::VariableDecl> {
        let name = format!("{}$snapshot${}", variable.name, version);
        let ty = variable.ty.create_snapshot(self)?;
        self.create_variable(name, ty)
    }
}

pub(in super::super) trait SnapshotsInterface {
    fn encode_snapshot_domain_name(&mut self, ty: &vir_mid::Type) -> SpannedEncodingResult<String>;
    fn encode_snapshot_constructor_name(
        &mut self,
        ty: &vir_mid::Type,
    ) -> SpannedEncodingResult<String>;
    fn encode_snapshot_domain(
        &mut self,
        ty: &vir_mid::Type,
    ) -> SpannedEncodingResult<vir_low::Type>;
    fn encode_snapshot_to_bytes_function(
        &mut self,
        ty: &vir_mid::Type,
    ) -> SpannedEncodingResult<()>;
    fn encode_snapshot_validity_expression(
        &mut self,
        argument: vir_low::Expression,
        ty: &vir_mid::Type,
    ) -> SpannedEncodingResult<vir_low::Expression>;
    fn encode_validity_axioms(&mut self, ty: &vir_mid::Type) -> SpannedEncodingResult<()>;
    fn encode_field_snapshot(
        &mut self,
        base_type: &vir_mid::Type,
        field: &vir_mid::FieldDecl,
        base_snapshot: vir_low::Expression,
        position: vir_mid::Position,
    ) -> SpannedEncodingResult<vir_low::Expression>;
    fn encode_snapshot_constant_constructor_call(
        &mut self,
        ty: &vir_mid::Type,
        argument: vir_low::Expression,
        position: vir_mid::Position,
    ) -> SpannedEncodingResult<vir_low::Expression>;
    fn encode_snapshot_update(
        &mut self,
        statements: &mut Vec<vir_low::Statement>,
        target: &vir_mid::Expression,
        value: vir_low::Expression,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<()>;
    fn new_snapshot_variable_version(
        &mut self,
        variable: &vir_mid::VariableDecl,
    ) -> SpannedEncodingResult<vir_low::VariableDecl>;
    fn current_snapshot_variable_version(
        &mut self,
        variable: &vir_mid::VariableDecl,
    ) -> SpannedEncodingResult<vir_low::VariableDecl>;
}

impl<'p, 'v: 'p, 'tcx: 'v> SnapshotsInterface for Lowerer<'p, 'v, 'tcx> {
    fn encode_snapshot_domain_name(&mut self, ty: &vir_mid::Type) -> SpannedEncodingResult<String> {
        Ok(format!("Snap${}", ty.get_identifier()))
    }
    fn encode_snapshot_constructor_name(
        &mut self,
        ty: &vir_mid::Type,
    ) -> SpannedEncodingResult<String> {
        Ok(format!("snap_constructor${}", ty.get_identifier()))
    }
    fn encode_snapshot_domain(
        &mut self,
        ty: &vir_mid::Type,
    ) -> SpannedEncodingResult<vir_low::Type> {
        let domain_name = self.encode_snapshot_domain_name(ty)?;
        self.domain_type(domain_name)
    }
    fn encode_snapshot_to_bytes_function(
        &mut self,
        ty: &vir_mid::Type,
    ) -> SpannedEncodingResult<()> {
        if !self.snapshots_state.encoded_to_bytes.contains(ty) {
            self.snapshots_state.encoded_to_bytes.insert(ty.clone());
            let domain_name = self.encode_snapshot_domain_name(ty)?;
            let domain_type = self.encode_snapshot_domain_type(ty)?;
            let return_type = self.bytes_type()?;
            self.declare_domain_function(
                std::borrow::Cow::Owned(domain_name),
                std::borrow::Cow::Owned(format!("to_bytes${}", ty.get_identifier())),
                std::borrow::Cow::Owned(vec![vir_low::VariableDecl::new("snapshot", domain_type)]),
                std::borrow::Cow::Owned(return_type),
            )?;
        }
        Ok(())
    }
    fn encode_snapshot_validity_expression(
        &mut self,
        argument: vir_low::Expression,
        ty: &vir_mid::Type,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        let domain_name = self.encode_snapshot_domain_name(ty)?;
        self.create_domain_func_app(
            domain_name,
            format!("valid${}", ty.get_identifier()),
            vec![argument],
            vir_low::Type::Bool,
            Default::default(),
        )
    }
    fn encode_validity_axioms(&mut self, ty: &vir_mid::Type) -> SpannedEncodingResult<()> {
        use vir_low::macros::*;
        let type_decl = self.encoder.get_type_decl_mid(ty)?;
        match &type_decl {
            // TODO: Refactor to remove code duplication with
            // prusti-viper/src/encoder/middle/core_proof/lower/predicates/interface.rs
            // and
            // prusti-viper/src/encoder/middle/core_proof/lower/fold_unfold/interface.rs
            vir_mid::TypeDecl::Bool => {
                let true_snapshot = self.encode_snapshot_constant_constructor_call(
                    ty,
                    true.into(),
                    Default::default(),
                )?;
                let false_snapshot = self.encode_snapshot_constant_constructor_call(
                    ty,
                    false.into(),
                    Default::default(),
                )?;
                let body = vir_low::Expression::and(
                    self.encode_snapshot_validity_expression(true_snapshot, ty)?,
                    self.encode_snapshot_validity_expression(false_snapshot, ty)?,
                );
                self.insert_validity_axiom(ty, body)?;
            }
            vir_mid::TypeDecl::Int(decl) => {
                use vir_low::macros::*;
                let variable = var! { variable: Int};
                let snapshot = self.encode_snapshot_constant_constructor_call(
                    ty,
                    variable.clone().into(),
                    Default::default(),
                )?;
                let snapshot_valid = self.encode_snapshot_validity_expression(snapshot, ty)?;
                let mut conjuncts = Vec::new();
                if let Some(lower_bound) = &decl.lower_bound {
                    conjuncts.push(expr! { [lower_bound.clone().to_low(self)? ] <= variable });
                }
                if let Some(upper_bound) = &decl.upper_bound {
                    conjuncts.push(expr! { variable <= [upper_bound.clone().to_low(self)? ] });
                }
                let body = vir_low::Expression::forall(
                    vec![variable],
                    vec![vir_low::Trigger::new(vec![snapshot_valid.clone()])],
                    vir_low::Expression::equals(snapshot_valid, conjuncts.into_iter().conjoin()),
                );
                self.insert_validity_axiom(ty, body)?;
            }
            vir_mid::TypeDecl::Float(_) => {
                unimplemented!();
            }
            // vir_mid::TypeDecl::TypeVar(TypeVar) => {},
            vir_mid::TypeDecl::Tuple(decl) => {
                self.encode_validity_axioms_with_fields(ty, decl.iter_fields())?;
            }
            vir_mid::TypeDecl::Struct(decl) => {
                self.encode_validity_axioms_with_fields(ty, decl.iter_fields())?;
            }
            // vir_mid::TypeDecl::Enum(Enum) => {},
            // vir_mid::TypeDecl::Array(Array) => {},
            // vir_mid::TypeDecl::Reference(Reference) => {},
            // vir_mid::TypeDecl::Never => {},
            // vir_mid::TypeDecl::Closure(Closure) => {},
            // vir_mid::TypeDecl::Unsupported(Unsupported) => {},
            x => unimplemented!("{}", x),
        }
        Ok(())
    }
    fn encode_field_snapshot(
        &mut self,
        base_type: &vir_mid::Type,
        field: &vir_mid::FieldDecl,
        base_snapshot: vir_low::Expression,
        position: vir_mid::Position,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        let domain_name = self.encode_snapshot_domain_name(base_type)?;
        let function_name = format!("snap_field${}${}", base_type.get_identifier(), field.name);
        let return_type = self.encode_snapshot_domain_type(&field.ty)?;
        self.create_domain_func_app(
            domain_name,
            function_name,
            vec![base_snapshot],
            return_type,
            position,
        )
    }
    fn encode_snapshot_constant_constructor_call(
        &mut self,
        ty: &vir_mid::Type,
        mut argument: vir_low::Expression,
        position: vir_mid::Position,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        let domain_name = self.encode_snapshot_domain_name(ty)?;
        let function_name = self.encode_snapshot_constructor_name(ty)?;
        let return_type = ty.create_snapshot(self)?;
        let low_type = match &ty {
            vir_mid::Type::Bool => vir_low::Type::Bool,
            vir_mid::Type::Int(_) => vir_low::Type::Int,
            x => unimplemented!("{:?}", x),
        };
        vir_low::operations::ty::Typed::set_type(&mut argument, low_type);
        self.create_domain_func_app(
            domain_name,
            function_name,
            vec![argument],
            return_type,
            position,
        )
    }
    fn encode_snapshot_update(
        &mut self,
        statements: &mut Vec<vir_low::Statement>,
        target: &vir_mid::Expression,
        value: vir_low::Expression,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<()> {
        use vir_low::macros::*;
        let base = target.get_base();
        let old_snapshot = base.create_snapshot(self)?;
        let new_snapshot = self.new_snapshot_variable_version(&base)?;
        self.snapshot_copy_except(statements, old_snapshot, new_snapshot, target, position)?;
        statements.push(stmtp! { position => assume ([target.create_snapshot(self)?] == [value]) });
        Ok(())
    }
    fn new_snapshot_variable_version(
        &mut self,
        variable: &vir_mid::VariableDecl,
    ) -> SpannedEncodingResult<vir_low::VariableDecl> {
        let versions = &mut self.snapshots_state.snapshot_variable_versions;
        let new_version = if versions.contains_key(&variable.name) {
            let version = versions.get_mut(&variable.name).unwrap();
            *version += 1;
            *version
        } else {
            versions.insert(variable.name.clone(), 1);
            1
        };
        self.create_snapshot_variable(variable, new_version)
    }
    fn current_snapshot_variable_version(
        &mut self,
        variable: &vir_mid::VariableDecl,
    ) -> SpannedEncodingResult<vir_low::VariableDecl> {
        let version = self
            .snapshots_state
            .snapshot_variable_versions
            .get(&variable.name)
            .cloned()
            .unwrap_or(0);
        self.create_snapshot_variable(variable, version)
    }
}
