use crate::encoder::{
    errors::SpannedEncodingResult,
    middle::core_proof::{
        adts::AdtsInterface,
        lowerer::Lowerer,
        snapshots::{valid_call, valid_call2, SnapshotValuesInterface},
    },
};
use vir_crate::low::{self as vir_low};

pub(in super::super::super) trait SnapshotAdtsInterface {
    // Names.

    fn snapshot_destructor_constant_name(
        &mut self,
        domain_name: &str,
    ) -> SpannedEncodingResult<String>;
    fn snapshot_constructor_struct_name(
        &mut self,
        domain_name: &str,
    ) -> SpannedEncodingResult<String>;
    /// Sometimes the same value can be constructed by multiple constructors.
    /// This method allows constructing alternative contructor's name.
    fn snapshot_constructor_struct_alternative_name(
        &mut self,
        domain_name: &str,
        variant: &str,
    ) -> SpannedEncodingResult<String>;
    fn snapshot_constructor_enum_variant_name(
        &mut self,
        domain_name: &str,
        variant_name: &str,
    ) -> SpannedEncodingResult<String>;

    // Calls.

    fn snapshot_constructor_constant_call(
        &mut self,
        domain_name: &str,
        arguments: Vec<vir_low::Expression>,
    ) -> SpannedEncodingResult<vir_low::Expression>;
    fn snapshot_alternative_constructor_struct_call(
        &mut self,
        domain_name: &str,
        variant_name: &str,
        arguments: Vec<vir_low::Expression>,
    ) -> SpannedEncodingResult<vir_low::Expression>;
    fn snapshot_destructor_struct_call(
        &mut self,
        domain_name: &str,
        field_name: &str,
        field_type: vir_low::Type,
        argument: vir_low::Expression,
    ) -> SpannedEncodingResult<vir_low::Expression>;
    fn snapshot_destructor_enum_variant_call(
        &mut self,
        domain_name: &str,
        variant: &str,
        variant_type: vir_low::Type,
        argument: vir_low::Expression,
    ) -> SpannedEncodingResult<vir_low::Expression>;

    // Registration.

    fn register_constant_constructor(
        &mut self,
        domain_name: &str,
        parameter_type: vir_low::Type,
    ) -> SpannedEncodingResult<()>;
    fn register_struct_constructor(
        &mut self,
        domain_name: &str,
        parameters: Vec<vir_low::VariableDecl>,
    ) -> SpannedEncodingResult<()>;
    /// If `use_main_constructor_destructors` is `true`, then uses destructors
    /// with `variant_name == ""`.
    fn register_alternative_constructor(
        &mut self,
        domain_name: &str,
        variant_name: &str,
        use_main_constructor_destructors: bool,
        parameters: Vec<vir_low::VariableDecl>,
    ) -> SpannedEncodingResult<()>;
    fn register_alternative_constructor_with_injectivity_axioms(
        &mut self,
        domain_name: &str,
        variant_name: &str,
        use_main_constructor_destructors: bool,
        parameters: Vec<vir_low::VariableDecl>,
    ) -> SpannedEncodingResult<()>;
    fn register_enum_variant_constructor(
        &mut self,
        domain_name: &str,
        variant_name: &str,
        variant_domain_name: &str,
        discriminant: vir_low::Expression,
    ) -> SpannedEncodingResult<()>;
}

impl<'p, 'v: 'p, 'tcx: 'v> SnapshotAdtsInterface for Lowerer<'p, 'v, 'tcx> {
    fn snapshot_destructor_constant_name(
        &mut self,
        domain_name: &str,
    ) -> SpannedEncodingResult<String> {
        self.adt_destructor_main_name(domain_name, "value")
    }
    fn snapshot_constructor_struct_name(
        &mut self,
        domain_name: &str,
    ) -> SpannedEncodingResult<String> {
        self.adt_constructor_main_name(domain_name)
    }
    fn snapshot_constructor_struct_alternative_name(
        &mut self,
        domain_name: &str,
        variant_name: &str,
    ) -> SpannedEncodingResult<String> {
        self.adt_constructor_variant_name(domain_name, variant_name)
    }
    fn snapshot_constructor_enum_variant_name(
        &mut self,
        domain_name: &str,
        variant_name: &str,
    ) -> SpannedEncodingResult<String> {
        self.adt_constructor_variant_name(domain_name, variant_name)
    }
    fn snapshot_constructor_constant_call(
        &mut self,
        domain_name: &str,
        arguments: Vec<vir_low::Expression>,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        self.adt_constructor_main_call(domain_name, arguments)
    }
    fn snapshot_alternative_constructor_struct_call(
        &mut self,
        domain_name: &str,
        variant_name: &str,
        arguments: Vec<vir_low::Expression>,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        self.adt_constructor_variant_call(domain_name, variant_name, arguments)
    }
    fn snapshot_destructor_struct_call(
        &mut self,
        domain_name: &str,
        field_name: &str,
        field_type: vir_low::Type,
        argument: vir_low::Expression,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        self.adt_destructor_main_call(domain_name, field_name, field_type, argument)
    }
    fn snapshot_destructor_enum_variant_call(
        &mut self,
        domain_name: &str,
        variant_name: &str,
        variant_type: vir_low::Type,
        argument: vir_low::Expression,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        self.adt_destructor_variant_call(domain_name, variant_name, "value", variant_type, argument)
    }
    fn register_constant_constructor(
        &mut self,
        domain_name: &str,
        parameter_type: vir_low::Type,
    ) -> SpannedEncodingResult<()> {
        use vir_low::macros::*;
        self.adt_register_main_constructor(
            domain_name,
            vars! { value: {parameter_type}},
            true,
            Some(valid_call2),
        )
    }
    fn register_struct_constructor(
        &mut self,
        domain_name: &str,
        parameters: Vec<vir_low::VariableDecl>,
    ) -> SpannedEncodingResult<()> {
        self.adt_register_main_constructor(domain_name, parameters, true, Some(valid_call2))
    }
    fn register_alternative_constructor(
        &mut self,
        domain_name: &str,
        variant_name: &str,
        use_main_constructor_destructors: bool,
        parameters: Vec<vir_low::VariableDecl>,
    ) -> SpannedEncodingResult<()> {
        self.adt_register_variant_constructor(
            domain_name,
            variant_name,
            use_main_constructor_destructors,
            parameters,
            false,
            None::<fn(&_, &_) -> SpannedEncodingResult<(vir_low::Expression, vir_low::Expression)>>,
        )
    }
    fn register_alternative_constructor_with_injectivity_axioms(
        &mut self,
        domain_name: &str,
        variant_name: &str,
        use_main_constructor_destructors: bool,
        parameters: Vec<vir_low::VariableDecl>,
    ) -> SpannedEncodingResult<()> {
        self.adt_register_variant_constructor(
            domain_name,
            variant_name,
            use_main_constructor_destructors,
            parameters,
            true,
            Some(valid_call2),
        )
    }
    fn register_enum_variant_constructor(
        &mut self,
        domain_name: &str,
        variant_name: &str,
        variant_domain_name: &str,
        discriminant: vir_low::Expression,
    ) -> SpannedEncodingResult<()> {
        use vir_low::macros::*;
        let parameter_type = vir_low::Type::domain(variant_domain_name.to_string());
        let discriminant_name = self.encode_discriminant_name(domain_name)?;
        let valid_call_with_discriminant =
            move |domain_name: &str, variable: &vir_low::VariableDecl| {
                let validity_call = valid_call(domain_name, variable)?;
                let discriminant_call = vir_low::Expression::domain_function_call(
                    domain_name,
                    discriminant_name,
                    vec![variable.clone().into()],
                    vir_low::Type::Int,
                );
                let guard =
                    expr! { [validity_call.clone()] && ([discriminant_call] == [discriminant]) };
                Ok((validity_call, guard))
            };
        self.adt_register_variant_constructor(
            domain_name,
            variant_name,
            false,
            vars! { value: {parameter_type}},
            true,
            Some(valid_call_with_discriminant),
        )
    }
}
