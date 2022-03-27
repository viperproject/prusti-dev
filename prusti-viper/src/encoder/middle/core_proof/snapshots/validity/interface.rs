use crate::encoder::{
    errors::SpannedEncodingResult,
    middle::core_proof::{
        adts::AdtsInterface,
        lowerer::{DomainsLowererInterface, Lowerer},
        snapshots::{SnapshotAdtsInterface, SnapshotDomainsInterface, SnapshotValuesInterface},
    },
};
use vir_crate::{
    common::expression::{ExpressionIterator, QuantifierHelpers},
    low::{self as vir_low},
    middle::{self as vir_mid},
};

pub(in super::super::super) fn valid_call(
    domain_name: &str,
    variable: &vir_low::VariableDecl,
) -> SpannedEncodingResult<vir_low::Expression> {
    Ok(vir_low::Expression::domain_function_call(
        domain_name,
        format!("valid${}", domain_name),
        vec![variable.clone().into()],
        vir_low::Type::Bool,
    ))
}

pub(in super::super::super) fn valid_call2(
    domain_name: &str,
    variable: &vir_low::VariableDecl,
) -> SpannedEncodingResult<(vir_low::Expression, vir_low::Expression)> {
    let call = valid_call(domain_name, variable)?;
    Ok((call.clone(), call))
}

fn get_non_primitive_domain(ty: &vir_low::Type) -> Option<&str> {
    if let vir_low::Type::Domain(domain) = ty {
        if domain.name != "Address" {
            return Some(&domain.name);
        }
    }
    None
}

pub(in super::super::super) trait SnapshotValidityInterface {
    fn encode_snapshot_valid_call_for_type(
        &mut self,
        argument: vir_low::Expression,
        ty: &vir_mid::Type,
    ) -> SpannedEncodingResult<vir_low::Expression>;
    fn encode_snapshot_valid_call(
        &mut self,
        domain_name: &str,
        argument: vir_low::Expression,
    ) -> SpannedEncodingResult<vir_low::Expression>;
    fn encode_validity_axioms_primitive(
        &mut self,
        domain_name: &str,
        parameter_type: vir_low::Type,
        invariant: vir_low::Expression,
    ) -> SpannedEncodingResult<()>;
    fn encode_validity_axioms_struct(
        &mut self,
        domain_name: &str,
        parameters: Vec<vir_low::VariableDecl>,
        invariant: vir_low::Expression,
    ) -> SpannedEncodingResult<()>;
    /// `variants` is `(variant_name, variant_domain, discriminant)`.
    fn encode_validity_axioms_enum(
        &mut self,
        ty: &vir_mid::Type,
        domain_name: &str,
        variants: Vec<(String, String, vir_low::Expression)>,
        invariant: vir_low::Expression,
        discriminant_bounds: vir_low::Expression,
    ) -> SpannedEncodingResult<()>;
    fn encode_validity_axioms_enum_variant(
        &mut self,
        ty: &vir_mid::Type,
        domain_name: &str,
        variant_name: String,
        variant_domain: String,
        discriminant: vir_low::Expression,
        invariant: vir_low::Expression,
    ) -> SpannedEncodingResult<()>;
}

impl<'p, 'v: 'p, 'tcx: 'v> SnapshotValidityInterface for Lowerer<'p, 'v, 'tcx> {
    fn encode_snapshot_valid_call_for_type(
        &mut self,
        argument: vir_low::Expression,
        ty: &vir_mid::Type,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        let domain_name = self.encode_snapshot_domain_name(ty)?;
        self.encode_snapshot_valid_call(&domain_name, argument)
    }
    fn encode_snapshot_valid_call(
        &mut self,
        domain_name: &str,
        argument: vir_low::Expression,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        self.create_domain_func_app(
            domain_name,
            format!("valid${}", domain_name),
            vec![argument],
            vir_low::Type::Bool,
            Default::default(),
        )
    }
    fn encode_validity_axioms_primitive(
        &mut self,
        domain_name: &str,
        parameter_type: vir_low::Type,
        invariant: vir_low::Expression,
    ) -> SpannedEncodingResult<()> {
        use vir_low::macros::*;
        let parameters = vars! { value: {parameter_type}};
        self.encode_validity_axioms_struct(domain_name, parameters, invariant)
    }
    fn encode_validity_axioms_struct(
        &mut self,
        domain_name: &str,
        parameters: Vec<vir_low::VariableDecl>,
        invariant: vir_low::Expression,
    ) -> SpannedEncodingResult<()> {
        use vir_low::macros::*;
        let mut valid_parameters = Vec::new();
        for parameter in &parameters {
            if let Some(domain_name) = get_non_primitive_domain(&parameter.ty) {
                valid_parameters.push(valid_call(domain_name, parameter)?);
            }
        }
        let constructor_call = self.adt_constructor_main_call(
            domain_name,
            parameters
                .iter()
                .map(|parameter| parameter.clone().into())
                .collect(),
        )?;
        let valid_constructor = self.encode_snapshot_valid_call(domain_name, constructor_call)?;
        if parameters.is_empty() {
            let axiom = vir_low::DomainAxiomDecl {
                name: format!("{}$validity_axiom_bottom_up", domain_name),
                body: expr! { [ valid_constructor ] == [ invariant ] },
            };
            self.declare_axiom(domain_name, axiom)?;
            return Ok(());
        }
        let mut conjuncts = vec![invariant]; // FIXME: We need to replace the fields here.
        conjuncts.extend(valid_parameters.clone());
        let validity_expression = conjuncts.into_iter().conjoin();
        if parameters
            .iter()
            .any(|parameter| get_non_primitive_domain(&parameter.ty).is_some())
        {
            // The top-down axiom allows proving that any of the fields is valid
            // if we know that the whole data strucure is valid. With no
            // parameters, the bottom-up and top-down axioms are equivalent.
            let mut top_down_validity_expression = validity_expression.clone();
            var_decls! { snapshot: {vir_low::Type::domain(domain_name.to_string())}};
            let valid_constructor =
                self.encode_snapshot_valid_call(domain_name, snapshot.clone().into())?;
            let mut triggers = Vec::new();
            for parameter in &parameters {
                if let Some(parameter_domain) = get_non_primitive_domain(&parameter.ty) {
                    let field = self.snapshot_destructor_struct_call(
                        domain_name,
                        &parameter.name,
                        parameter.ty.clone(),
                        snapshot.clone().into(),
                    )?;
                    top_down_validity_expression = top_down_validity_expression
                        .replace_place(&parameter.clone().into(), &field);
                    let valid_field = self.encode_snapshot_valid_call(parameter_domain, field)?;
                    triggers.push(vir_low::Trigger::new(vec![
                        valid_constructor.clone(),
                        valid_field.clone(),
                    ]));
                }
            }
            let axiom_top_down_body = vir_low::Expression::forall(
                vec![snapshot],
                triggers,
                expr! {
                    [ valid_constructor ] == [ top_down_validity_expression ]
                },
            );
            let axiom_top_down = vir_low::DomainAxiomDecl {
                name: format!("{}$validity_axiom_top_down", domain_name),
                body: axiom_top_down_body,
            };
            self.declare_axiom(domain_name, axiom_top_down)?;
        }
        let axiom_bottom_up_body = {
            let mut trigger = vec![valid_constructor.clone()];
            trigger.extend(valid_parameters.clone());
            vir_low::Expression::forall(
                parameters,
                vec![vir_low::Trigger::new(trigger)],
                expr! {
                    [ valid_constructor ] == [ validity_expression ]
                },
            )
        };
        // The axiom that allows proving that the data structure is
        // valid if we know that its fields are valid.
        let axiom_bottom_up = vir_low::DomainAxiomDecl {
            name: format!("{}$validity_axiom_bottom_up", domain_name),
            body: axiom_bottom_up_body,
        };
        self.declare_axiom(domain_name, axiom_bottom_up)?;
        Ok(())
    }
    fn encode_validity_axioms_enum(
        &mut self,
        ty: &vir_mid::Type,
        domain_name: &str,
        variants: Vec<(String, String, vir_low::Expression)>,
        invariant: vir_low::Expression,
        discriminant_bounds: vir_low::Expression,
    ) -> SpannedEncodingResult<()> {
        // We generate a single top-down validity axiom for all variants.
        {
            use vir_low::macros::*;
            var_decls! { snapshot: {vir_low::Type::domain(domain_name.to_string())}};
            let valid_constructor =
                self.encode_snapshot_valid_call(domain_name, snapshot.clone().into())?;
            let mut triggers = Vec::new();
            let mut valid_variants = Vec::new();
            let discriminant_call =
                self.obtain_enum_discriminant(snapshot.clone().into(), ty, Default::default())?;
            for (variant_name, variant_domain, discriminant) in &variants {
                let variant_type = vir_low::Type::domain(variant_domain.clone());
                let variant = self.snapshot_destructor_enum_variant_call(
                    domain_name,
                    variant_name,
                    variant_type,
                    snapshot.clone().into(),
                )?;
                let valid_variant = self.encode_snapshot_valid_call(variant_domain, variant)?;
                triggers.push(vir_low::Trigger::new(vec![
                    valid_constructor.clone(),
                    valid_variant.clone(),
                ]));
                valid_variants.push(expr! {
                    ([ discriminant_call.clone() ] == [ discriminant.clone() ]) ==> [ valid_variant ]
                });
            }
            let discriminant_bounds = discriminant_bounds.replace_discriminant(&discriminant_call);
            triggers.push(vir_low::Trigger::new(vec![
                valid_constructor.clone(),
                discriminant_call,
            ]));
            let axiom_top_down_body = vir_low::Expression::forall(
                vec![snapshot],
                triggers,
                expr! {
                    [ valid_constructor ] == (
                        [ discriminant_bounds ] && [ valid_variants.into_iter().conjoin() ]
                    )
                },
            );
            let axiom_top_down = vir_low::DomainAxiomDecl {
                name: format!("{}$validity_axiom_top_down", domain_name),
                body: axiom_top_down_body,
            };
            self.declare_axiom(domain_name, axiom_top_down)?;
        }
        // We generate a separate bottom-up validity axiom for each variant.
        for (variant_name, variant_domain, discriminant) in variants {
            self.encode_validity_axioms_enum_variant(
                ty,
                domain_name,
                variant_name,
                variant_domain,
                discriminant,
                invariant.clone(),
            )?;
        }
        Ok(())
    }
    fn encode_validity_axioms_enum_variant(
        &mut self,
        ty: &vir_mid::Type,
        domain_name: &str,
        variant_name: String,
        variant_domain: String,
        discriminant: vir_low::Expression,
        invariant: vir_low::Expression,
    ) -> SpannedEncodingResult<()> {
        use vir_low::macros::*;
        let variant_type = vir_low::Type::domain(variant_domain.clone());
        var_decls! { variant: {variant_type} };
        let constructor_call = self.adt_constructor_variant_call(
            domain_name,
            &variant_name,
            vec![variant.clone().into()],
        )?;
        let valid_constructor =
            self.encode_snapshot_valid_call(domain_name, constructor_call.clone())?;
        let valid_variant =
            self.encode_snapshot_valid_call(&variant_domain, variant.clone().into())?;
        let axiom_bottom_up_body = {
            let trigger = vec![valid_variant.clone(), valid_constructor.clone()];
            vir_low::Expression::forall(
                vec![variant.clone()],
                vec![vir_low::Trigger::new(trigger)],
                expr! {
                    [ valid_constructor ] == ([ valid_variant ] && [ invariant ])
                },
            )
        };
        // The axiom that allows proving that the data structure is
        // valid if we know that its fields are valid.
        let validity_axiom_bottom_up = vir_low::DomainAxiomDecl {
            name: format!("{}${}$validity_axiom_bottom_up", domain_name, variant_name),
            body: axiom_bottom_up_body,
        };
        self.declare_axiom(domain_name, validity_axiom_bottom_up)?;
        let discriminant_axiom_body = {
            let discriminant_call =
                self.obtain_enum_discriminant(constructor_call.clone(), ty, Default::default())?;
            vir_low::Expression::forall(
                vec![variant],
                vec![vir_low::Trigger::new(vec![constructor_call])],
                expr! {
                    [ discriminant_call ] == [ discriminant ]
                },
            )
        };
        // The axiom that defines the discriminant of the variant.
        let dicsriminant_axiom = vir_low::DomainAxiomDecl {
            name: format!("{}${}$discriminant_axiom", domain_name, variant_name),
            body: discriminant_axiom_body,
        };
        self.declare_axiom(domain_name, dicsriminant_axiom)?;
        Ok(())
    }
}
