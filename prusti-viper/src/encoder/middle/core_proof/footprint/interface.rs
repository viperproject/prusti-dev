use crate::encoder::{
    errors::SpannedEncodingResult,
    middle::core_proof::{lowerer::Lowerer, snapshots::IntoSnapshot},
};
use rustc_hash::FxHashMap;
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
            vir_mid::Predicate::UniqueRef(predicate) => {
                unimplemented!("predicate: {}", predicate);
            }
            vir_mid::Predicate::UniqueRefRange(predicate) => {
                unimplemented!("predicate: {}", predicate);
            }
            vir_mid::Predicate::FracRef(predicate) => {
                unimplemented!("predicate: {}", predicate);
            }
            vir_mid::Predicate::FracRefRange(predicate) => {
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

fn compute_parameter_name(
    place: &vir_mid::Expression,
    parameter_name: &mut String,
    func_app_names: &mut FxHashMap<vir_mid::FuncApp, String>,
) -> SpannedEncodingResult<()> {
    match place {
        vir_mid::Expression::Deref(expression) => {
            compute_parameter_name(&expression.base, parameter_name, func_app_names)?;
            parameter_name.push_str("$deref");
        }
        vir_mid::Expression::Field(expression) => {
            compute_parameter_name(&expression.base, parameter_name, func_app_names)?;
            parameter_name.push('$');
            parameter_name.push_str(&expression.field.name);
        }
        vir_mid::Expression::Local(expression) => {
            assert!(expression.variable.is_self_variable());
        }
        vir_mid::Expression::FuncApp(expression) => {
            if !func_app_names.contains_key(expression) {
                let name = format!("$func_app${}", func_app_names.len());
                func_app_names.insert(expression.clone(), name);
            }
            parameter_name.push_str(&func_app_names[expression]);
        }
        _ => {
            unimplemented!("{place}");
        }
    }
    Ok(())
}

impl<'p, 'v: 'p, 'tcx: 'v> Lowerer<'p, 'v, 'tcx> {
    /// Computes the parameter that corresponds to the value of
    /// the dereferenced place.
    fn compute_deref_field_from_place(
        &mut self,
        place: &vir_mid::Expression,
        func_app_names: &mut FxHashMap<vir_mid::FuncApp, String>,
    ) -> SpannedEncodingResult<(String, vir_low::Type)> {
        let mut parameter_name = String::new();
        compute_parameter_name(place, &mut parameter_name, func_app_names)?;
        Ok((parameter_name, place.get_type().to_snapshot(self)?))
    }

    /// Computes the parameter that corresponds to the value of
    /// the dereferenced place.
    fn compute_deref_field_from_range_address(
        &mut self,
        address: &vir_mid::Expression,
        func_app_names: &mut FxHashMap<vir_mid::FuncApp, String>,
    ) -> SpannedEncodingResult<(String, vir_low::Type)> {
        let mut parameter_name = String::new();
        compute_parameter_name(address, &mut parameter_name, func_app_names)?;
        let vir_mid::Type::Pointer(ty) = address.get_type() else {
            unreachable!();
        };
        let element_type = ty.target_type.to_snapshot(self)?;
        Ok((parameter_name, vir_low::Type::seq(element_type)))
    }
}

pub(in super::super) struct DerefOwned {
    pub(in super::super) place: vir_mid::Expression,
    pub(in super::super) field_name: String,
    pub(in super::super) field_type: vir_low::Type,
}

pub(in super::super) struct DerefOwnedRange {
    pub(in super::super) address: vir_mid::Expression,
    pub(in super::super) field_name: String,
    pub(in super::super) field_type: vir_low::Type,
}

pub(in super::super) type DerefFields = (Vec<DerefOwned>, Vec<DerefOwnedRange>);

pub(in super::super) trait FootprintInterface {
    fn structural_invariant_to_deref_fields(
        &mut self,
        invariant: &[vir_mid::Expression],
    ) -> SpannedEncodingResult<DerefFields>;
}

impl<'p, 'v: 'p, 'tcx: 'v> FootprintInterface for Lowerer<'p, 'v, 'tcx> {
    /// For the given invariant, compute the deref fields. This is done by
    /// finding all `own` predicates and creating variables for them.
    ///
    /// The order of the returned fields is guaranteed to be the same for the
    /// same invariant.
    fn structural_invariant_to_deref_fields(
        &mut self,
        invariant: &[vir_mid::Expression],
    ) -> SpannedEncodingResult<DerefFields> {
        let mut func_app_names = FxHashMap::default();
        let mut owned_places = BTreeSet::default();
        let mut owned_range_addresses = BTreeSet::default();
        for expression in invariant {
            let (new_owned_places, new_owned_range_addresses) = expression.collect_owned_places();
            owned_places.extend(new_owned_places);
            owned_range_addresses.extend(new_owned_range_addresses);
        }
        let mut owned_fields = Vec::new();
        for owned_place in owned_places {
            let (name, ty) =
                self.compute_deref_field_from_place(&owned_place, &mut func_app_names)?;
            owned_fields.push(DerefOwned {
                place: owned_place,
                field_name: name,
                field_type: ty,
            });
        }
        let mut owned_range_fields = Vec::new();
        for owned_range_address in owned_range_addresses {
            let (name, ty) = self.compute_deref_field_from_range_address(
                &owned_range_address,
                &mut func_app_names,
            )?;
            owned_range_fields.push(DerefOwnedRange {
                address: owned_range_address,
                field_name: name,
                field_type: ty,
            });
        }
        Ok((owned_fields, owned_range_fields))
    }
}
