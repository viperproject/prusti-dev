use crate::encoder::{
    errors::SpannedEncodingResult,
    high::types::HighTypeEncoderInterface,
    middle::core_proof::{lowerer::Lowerer, snapshots::IntoSnapshot},
};
use std::collections::{BTreeMap, BTreeSet};
use vir_crate::{
    common::position::Positioned,
    low as vir_low,
    middle::{self as vir_mid, operations::ty::Typed, visitors::ExpressionFolder},
};

struct FootprintComputation<'l, 'p, 'v, 'tcx> {
    _lowerer: &'l mut Lowerer<'p, 'v, 'tcx>,
    // parameters: &'l BTreeMap<vir_mid::VariableDecl, &'l vir_mid::type_decl::Struct>,
    deref_field_fresh_index_counters: BTreeMap<vir_mid::VariableDecl, usize>,
    deref_field_indices: BTreeMap<vir_mid::VariableDecl, usize>,
    derefs: Vec<vir_mid::Deref>,
}

// FIXME: Delete.
impl<'l, 'p, 'v, 'tcx> FootprintComputation<'l, 'p, 'v, 'tcx> {
    fn new(
        lowerer: &'l mut Lowerer<'p, 'v, 'tcx>,
        parameters: &'l BTreeMap<vir_mid::VariableDecl, &'l vir_mid::type_decl::Struct>,
    ) -> Self {
        let deref_field_fresh_index_counters = parameters
            .iter()
            .map(|(parameter, decl)| (parameter.clone(), decl.fields.len()))
            .collect();
        Self {
            _lowerer: lowerer,
            // parameters,
            deref_field_fresh_index_counters,
            deref_field_indices: Default::default(),
            derefs: Default::default(),
        }
    }

    fn extract_base_variable<'a>(
        &self,
        place: &'a vir_mid::Expression,
    ) -> &'a vir_mid::VariableDecl {
        match place {
            vir_mid::Expression::Local(expression) => &expression.variable,
            _ => unimplemented!(),
        }
    }

    // FIXME: This should be using `own` places.
    fn create_deref_field(&mut self, deref: &vir_mid::Deref) -> vir_mid::Expression {
        match &*deref.base {
            vir_mid::Expression::Field(expression) => {
                let variable = self.extract_base_variable(&expression.base);
                let deref_field_name = format!("{}$deref", expression.field.name);
                let deref_variable = vir_mid::VariableDecl::new(deref_field_name, deref.ty.clone());
                let field_index = self.compute_deref_field_index(deref, variable, &deref_variable);
                vir_mid::Expression::field(
                    (*expression.base).clone(),
                    vir_mid::FieldDecl {
                        name: deref_variable.name,
                        index: field_index,
                        ty: deref_variable.ty,
                    },
                    expression.position,
                )
            }
            _ => unimplemented!(),
        }
    }

    fn compute_deref_field_index(
        &mut self,
        deref: &vir_mid::Deref,
        variable: &vir_mid::VariableDecl,
        deref_variable: &vir_mid::VariableDecl,
    ) -> usize {
        if let Some(index) = self.deref_field_indices.get(deref_variable) {
            *index
        } else {
            let counter = self
                .deref_field_fresh_index_counters
                .get_mut(variable)
                .unwrap();
            let index = *counter;
            *counter += 1;
            self.deref_field_indices
                .insert(deref_variable.clone(), index);
            self.derefs.push(deref.clone());
            index
        }
    }

    fn into_deref_fields(self) -> Vec<(vir_mid::VariableDecl, usize)> {
        let mut deref_fields: Vec<_> = self.deref_field_indices.into_iter().collect();
        deref_fields.sort_by_key(|(_, index)| *index);
        deref_fields
    }

    fn into_derefs(self) -> Vec<vir_mid::Deref> {
        self.derefs
    }
}

impl<'l, 'p, 'v, 'tcx> vir_mid::visitors::ExpressionFolder
    for FootprintComputation<'l, 'p, 'v, 'tcx>
{
    fn fold_acc_predicate_enum(
        &mut self,
        acc_predicate: vir_mid::AccPredicate,
    ) -> vir_mid::Expression {
        match *acc_predicate.predicate {
            vir_mid::Predicate::LifetimeToken(_) => {
                unimplemented!()
            }
            vir_mid::Predicate::MemoryBlockStack(_)
            | vir_mid::Predicate::MemoryBlockStackDrop(_)
            | vir_mid::Predicate::MemoryBlockHeap(_)
            | vir_mid::Predicate::MemoryBlockHeapRange(_)
            | vir_mid::Predicate::MemoryBlockHeapDrop(_) => true.into(),
            vir_mid::Predicate::OwnedNonAliased(predicate) => {
                let position = predicate.place.position();
                let place = self.fold_expression(predicate.place);
                vir_mid::Expression::builtin_func_app(
                    vir_mid::BuiltinFunc::IsValid,
                    Vec::new(),
                    vec![place],
                    vir_mid::Type::Bool,
                    position,
                )
                // match predicate.place {
                // vir_mid::Expression::Deref(deref) => {
                //     let deref_field = self.create_deref_field(&deref);
                //     let app = vir_mid::Expression::builtin_func_app(
                //         vir_mid::BuiltinFunc::IsValid,
                //         Vec::new(),
                //         vec![deref_field],
                //         vir_mid::Type::Bool,
                //         deref.position,
                //     );
                //     app
                // }}
                // _ => unimplemented!(),
            }
            vir_mid::Predicate::OwnedRange(predicate) => {
                unimplemented!("predicate: {}", predicate);
            }
            vir_mid::Predicate::OwnedSet(predicate) => {
                unimplemented!("predicate: {}", predicate);
            }
        }
    }

    fn fold_deref_enum(&mut self, deref: vir_mid::Deref) -> vir_mid::Expression {
        if deref.base.get_type().is_pointer() {
            self.create_deref_field(&deref)
        } else {
            vir_mid::Expression::Deref(self.fold_deref(deref))
        }
    }
}

struct Predicate<'l, 'p, 'v, 'tcx> {
    lowerer: &'l mut Lowerer<'p, 'v, 'tcx>,
}

impl<'l, 'p, 'v, 'tcx> Predicate<'l, 'p, 'v, 'tcx> {
    fn new(lowerer: &'l mut Lowerer<'p, 'v, 'tcx>) -> Self {
        Self { lowerer }
    }

    // FIXME: Code duplication.
    fn extract_base_variable<'a>(
        &self,
        place: &'a vir_mid::Expression,
    ) -> &'a vir_mid::VariableDecl {
        match place {
            vir_mid::Expression::Local(expression) => &expression.variable,
            _ => unimplemented!(),
        }
    }
}

impl<'l, 'p, 'v, 'tcx> vir_mid::visitors::ExpressionFolder for Predicate<'l, 'p, 'v, 'tcx> {
    // fn fold_field_enum(&mut self, field: vir_mid::Field) -> vir_mid::Expression {
    //     match &*field.base {
    //         vir_mid::Expression::Local(local) => {
    //             assert!(local.variable.is_self_variable());
    //             let position = field.position;
    //             let app = vir_mid::Expression::builtin_func_app(
    //                 vir_mid::BuiltinFunc::GetSnapshot,
    //                 Vec::new(),
    //                 vec![deref_field],
    //                 vir_mid::Type::Bool,
    //                 position,
    //             );
    //             app
    //         }
    //         _ => vir_mid::visitors::default_fold_field(self, field),
    //     }
    // }
    // fn fold_acc_predicate_enum(
    //     &mut self,
    //     acc_predicate: vir_mid::AccPredicate,
    // ) -> vir_mid::Expression {
    //     match *acc_predicate.predicate {
    //         vir_mid::Predicate::LifetimeToken(_) => {
    //             unimplemented!()
    //         }
    //         vir_mid::Predicate::MemoryBlockStack(_)
    //         | vir_mid::Predicate::MemoryBlockStackDrop(_)
    //         | vir_mid::Predicate::MemoryBlockHeap(_)
    //         | vir_mid::Predicate::MemoryBlockHeapDrop(_) => true.into(),
    //         vir_mid::Predicate::OwnedNonAliased(predicate) => match predicate.place {
    //             vir_mid::Expression::Deref(deref) => {
    //                 let deref_field = self.create_deref_field(&deref);
    //                 let app = vir_mid::Expression::builtin_func_app(
    //                     vir_mid::BuiltinFunc::IsValid,
    //                     Vec::new(),
    //                     vec![deref_field],
    //                     vir_mid::Type::Bool,
    //                     deref.position,
    //                 );
    //                 app
    //             }
    //             _ => unimplemented!(),
    //         },
    //     }
    // }
}

pub(in super::super) trait FootprintInterface {
    // fn purify_expressions(
    //     &mut self,
    //     expressions: Vec<vir_mid::Expression>,
    //     parameters: &BTreeMap<vir_mid::VariableDecl, &vir_mid::type_decl::Struct>,
    // ) -> SpannedEncodingResult<Vec<vir_mid::Expression>>;

    // /// Rewrite expression so that it is based only on the snapshots, removing
    // /// all predicates.
    // fn structural_invariant_to_pure_expression(
    //     &mut self,
    //     expressions: Vec<vir_mid::Expression>,
    //     ty: &vir_mid::Type,
    //     decl: &vir_mid::type_decl::Struct,
    //     fields: &mut Vec<vir_low::VariableDecl>,
    // ) -> SpannedEncodingResult<Vec<vir_mid::Expression>>;

    // fn structural_invariant_to_predicate_assertion(
    //     &mut self,
    //     expressions: Vec<vir_mid::Expression>,
    // ) -> SpannedEncodingResult<Vec<vir_mid::Expression>>;

    // fn framing_variable_deref_fields(
    //     &mut self,
    //     framing_variables: &[vir_mid::VariableDecl],
    // ) -> SpannedEncodingResult<Vec<(vir_mid::Expression, String, vir_low::Type)>>;

    fn structural_invariant_to_deref_fields(
        &mut self,
        invariant: &[vir_mid::Expression],
    ) -> SpannedEncodingResult<Vec<(vir_mid::Expression, String, vir_low::Type)>>;

    fn compute_deref_field_from_place(
        &mut self,
        place: &vir_mid::Expression,
    ) -> SpannedEncodingResult<(String, vir_low::Type)>;
}

impl<'p, 'v: 'p, 'tcx: 'v> FootprintInterface for Lowerer<'p, 'v, 'tcx> {
    // fn framing_variable_deref_fields(
    //     &mut self,
    //     framing_variables: &[vir_mid::VariableDecl],
    // ) -> SpannedEncodingResult<Vec<(vir_mid::Expression, String, vir_low::Type)>> {
    //     let mut deref_fields = Vec::new();
    //     for variable in framing_variables {
    //         let type_decl = self.encoder.get_type_decl_mid(&variable.ty)?;
    //         if let vir_mid::TypeDecl::Struct(vir_mid::type_decl::Struct {
    //             structural_invariant: Some(invariant),
    //             ..
    //         }) = &type_decl
    //         {
    //             deref_fields.extend(self.structural_invariant_to_deref_fields(invariant)?);
    //         }
    //     }
    //     Ok(deref_fields)
    // }

    /// For the given invariant, compute the deref fields. This is done by
    /// finding all `own` predicates and creating variables for them.
    ///
    /// The order of the returned fields is guaranteed to be the same for the
    /// same invariant.
    fn structural_invariant_to_deref_fields(
        &mut self,
        invariant: &[vir_mid::Expression],
    ) -> SpannedEncodingResult<Vec<(vir_mid::Expression, String, vir_low::Type)>> {
        let mut owned_places = BTreeSet::default();
        for expression in invariant {
            owned_places.extend(expression.collect_owned_places());
        }
        let mut fields = Vec::new();
        for owned_place in owned_places {
            let (name, ty) = self.compute_deref_field_from_place(&owned_place)?;
            fields.push((owned_place, name, ty));
        }
        Ok(fields)
    }

    /// Computes the parameter that corresponds to the value of
    /// the dereferenced place.
    fn compute_deref_field_from_place(
        &mut self,
        place: &vir_mid::Expression,
    ) -> SpannedEncodingResult<(String, vir_low::Type)> {
        let mut parameter_name = String::new();
        fn compute_name(
            place: &vir_mid::Expression,
            parameter_name: &mut String,
        ) -> SpannedEncodingResult<()> {
            match place {
                vir_mid::Expression::Deref(expression) => {
                    compute_name(&expression.base, parameter_name)?;
                    parameter_name.push_str("$deref");
                }
                vir_mid::Expression::Field(expression) => {
                    compute_name(&expression.base, parameter_name)?;
                    parameter_name.push('$');
                    parameter_name.push_str(&expression.field.name);
                }
                vir_mid::Expression::Local(expression) => {
                    assert!(expression.variable.is_self_variable());
                }
                _ => {
                    unimplemented!("{place}");
                }
            }
            Ok(())
        }
        compute_name(place, &mut parameter_name)?;
        Ok((parameter_name, place.get_type().to_snapshot(self)?))
    }
    // fn purify_expressions(
    //     &mut self,
    //     expressions: Vec<vir_mid::Expression>,
    //     parameters: &BTreeMap<vir_mid::VariableDecl, &vir_mid::type_decl::Struct>,
    // ) -> SpannedEncodingResult<Vec<vir_mid::Expression>> {
    //     let mut computation = FootprintComputation::new(self, parameters);
    //     let mut purified_expressions = Vec::with_capacity(expressions.len());
    //     for expression in expressions {
    //         purified_expressions.push(computation.fold_expression(expression));
    //     }
    //     Ok(purified_expressions)
    // }

    // FIXME: Delete.
    // fn structural_invariant_to_pure_expression(
    //     &mut self,
    //     expressions: Vec<vir_mid::Expression>,
    //     ty: &vir_mid::Type,
    //     decl: &vir_mid::type_decl::Struct,
    //     fields: &mut Vec<vir_low::VariableDecl>,
    // ) -> SpannedEncodingResult<Vec<vir_mid::Expression>> {
    //     let self_variable = vir_mid::VariableDecl::self_variable(ty.clone());
    //     let mut parameters = BTreeMap::new();
    //     parameters.insert(self_variable, decl);
    //     let mut computation = FootprintComputation::new(self, &parameters);
    //     let mut purified_expressions = Vec::with_capacity(expressions.len());
    //     for expression in expressions {
    //         purified_expressions.push(computation.fold_expression(expression));
    //     }
    //     let deref_fields = computation.into_deref_fields();
    //     for (deref_field, _) in deref_fields {
    //         fields.push(vir_low::VariableDecl::new(
    //             deref_field.name,
    //             deref_field.ty.to_snapshot(self)?,
    //         ));
    //     }
    //     Ok(purified_expressions)
    // }

    // fn structural_invariant_to_predicate_assertion(
    //     &mut self,
    //     expressions: Vec<vir_mid::Expression>,
    // ) -> SpannedEncodingResult<Vec<vir_mid::Expression>> {
    //     let mut converter = Predicate::new(self);
    //     let mut new_expressions = Vec::with_capacity(expressions.len());
    //     for expression in expressions {
    //         new_expressions.push(converter.fold_expression(expression));
    //     }
    //     Ok(new_expressions)
    // }
}
