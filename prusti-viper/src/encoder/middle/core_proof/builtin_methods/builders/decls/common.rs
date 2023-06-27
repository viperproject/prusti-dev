use crate::encoder::{
    errors::{BuiltinMethodKind, ErrorCtxt, SpannedEncodingResult},
    high::types::HighTypeEncoderInterface,
    middle::core_proof::{
        builtin_methods::{
            builders::calls::builder::BuiltinMethodCallBuilder, calls::interface::CallContext,
            BuiltinMethodsInterface,
        },
        const_generics::ConstGenericsInterface,
        errors::ErrorsInterface,
        lifetimes::LifetimesInterface,
        lowerer::Lowerer,
        predicates::PredicatesMemoryBlockInterface,
        snapshots::{IntoPureSnapshot, SnapshotValidityInterface, SnapshotValuesInterface},
        type_layouts::TypeLayoutsInterface,
    },
};
use vir_crate::{
    common::identifier::WithIdentifier,
    low::{self as vir_low},
    middle as vir_mid,
};

pub(in super::super::super::super) struct BuiltinMethodBuilder<'l, 'p, 'v, 'tcx> {
    pub(in super::super) lowerer: &'l mut Lowerer<'p, 'v, 'tcx>,
    pub(in super::super) kind: vir_low::MethodKind,
    pub(in super::super) method_name: &'l str,
    pub(in super::super) ty: &'l vir_mid::Type,
    pub(in super::super) type_decl: &'l vir_mid::TypeDecl,
    pub(in super::super) parameters: Vec<vir_low::VariableDecl>,
    pub(in super::super) targets: Vec<vir_low::VariableDecl>,
    pub(in super::super) pres: Vec<vir_low::Expression>,
    pub(in super::super) posts: Vec<vir_low::Expression>,
    pub(in super::super) statements: Option<Vec<vir_low::Statement>>,
    pub(in super::super) position: vir_low::Position,
}

impl<'l, 'p, 'v, 'tcx> BuiltinMethodBuilder<'l, 'p, 'v, 'tcx> {
    pub(in super::super::super::super) fn new(
        lowerer: &'l mut Lowerer<'p, 'v, 'tcx>,
        kind: vir_low::MethodKind,
        method_name: &'l str,
        ty: &'l vir_mid::Type,
        type_decl: &'l vir_mid::TypeDecl,
        error_kind: BuiltinMethodKind,
    ) -> SpannedEncodingResult<Self> {
        let span = lowerer.encoder.get_type_definition_span_mid(ty)?;
        let position = lowerer.register_error(span, ErrorCtxt::UnexpectedBuiltinMethod(error_kind));
        Ok(Self {
            kind,
            method_name,
            ty,
            type_decl,
            parameters: Vec::new(),
            targets: Vec::new(),
            pres: Vec::new(),
            posts: Vec::new(),
            statements: None,
            position,
            lowerer,
        })
    }

    pub(in super::super::super::super) fn build(self) -> vir_low::MethodDecl {
        vir_low::MethodDecl {
            kind: self.kind,
            name: format!("{}${}", self.method_name, self.ty.get_identifier()),
            parameters: self.parameters,
            targets: self.targets,
            pres: self.pres,
            posts: self.posts,
            body: self.statements,
        }
    }
}

impl<'l, 'p, 'v, 'tcx> BuiltinMethodBuilderMethods<'l, 'p, 'v, 'tcx>
    for BuiltinMethodBuilder<'l, 'p, 'v, 'tcx>
{
    fn inner(&mut self) -> &mut BuiltinMethodBuilder<'l, 'p, 'v, 'tcx> {
        self
    }
}

pub(in super::super::super::super) trait BuiltinMethodBuilderMethods<'l, 'p, 'v, 'tcx>:
    Sized
where
    'p: 'l,
    'v: 'p,
    'tcx: 'v,
{
    fn inner(&mut self) -> &mut BuiltinMethodBuilder<'l, 'p, 'v, 'tcx>;

    fn lowerer<'a>(&'a mut self) -> &'a mut Lowerer<'p, 'v, 'tcx>
    where
        'l: 'a,
    {
        self.inner().lowerer
    }

    fn add_precondition(&mut self, expression: vir_low::Expression) {
        self.inner().pres.push(expression);
    }

    fn add_postcondition(&mut self, expression: vir_low::Expression) {
        self.inner().posts.push(expression);
    }

    fn compute_address(
        &self,
        place: &vir_low::VariableDecl,
        root_address: &vir_low::VariableDecl,
    ) -> vir_low::Expression {
        self.compute_address_expression(place.clone().into(), root_address.clone().into())
    }

    fn compute_address_expression(
        &self,
        place: vir_low::Expression,
        root_address: vir_low::Expression,
    ) -> vir_low::Expression {
        use vir_low::macros::*;
        let compute_address = ty!(Address);
        expr! { ComputeAddress::compute_address([place], [root_address]) }
    }

    fn create_memory_block(
        &mut self,
        address: vir_low::Expression,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        self.create_memory_block_with_permission_amount(
            address,
            vir_low::Expression::full_permission(),
        )
    }

    fn create_memory_block_with_permission_amount(
        &mut self,
        address: vir_low::Expression,
        permission_amount: vir_low::Expression,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        use vir_low::macros::*;
        let inner = self.inner();
        let size_of = inner
            .lowerer
            .encode_type_size_expression2(inner.ty, inner.type_decl)?;
        Ok(expr! {
            acc(MemoryBlock([address], [size_of]), [permission_amount])
        })
    }

    fn create_memory_block_bytes(
        &mut self,
        address: vir_low::Expression,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        let inner = self.inner();
        let size_of = inner
            .lowerer
            .encode_type_size_expression2(inner.ty, inner.type_decl)?;
        inner
            .lowerer
            .encode_memory_block_bytes_expression(address, size_of)
    }

    fn create_permission_amount_positive(
        &mut self,
        permission_amount: &vir_low::VariableDecl,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        use vir_low::macros::*;
        Ok(expr! {
            [vir_low::Expression::no_permission()] < [permission_amount.clone().into()]
        })
    }

    fn create_lifetime_parameters(&mut self) -> SpannedEncodingResult<()> {
        let inner = self.inner();
        let parameters = inner.lowerer.create_lifetime_parameters(inner.type_decl)?;
        inner.parameters.extend(parameters);
        Ok(())
    }

    fn create_const_parameters(&mut self) -> SpannedEncodingResult<()> {
        let inner = self.inner();
        let parameters = inner.lowerer.create_const_parameters(inner.type_decl)?;
        inner.parameters.extend(parameters);
        Ok(())
    }

    fn add_const_parameters_validity_precondition(&mut self) -> SpannedEncodingResult<()> {
        let inner = self.inner();
        let size_type = inner.lowerer.size_type_mid()?;
        for parameter_mid in inner.type_decl.get_const_parameters() {
            let parameter = parameter_mid.to_pure_snapshot(inner.lowerer)?;
            let validity = inner
                .lowerer
                .encode_snapshot_valid_call_for_type(parameter.into(), &size_type)?;
            inner.add_precondition(validity);
        }
        Ok(())
    }

    fn create_body(&mut self) {
        let inner = self.inner();
        debug_assert!(inner.statements.is_none(), "The body is already created.");
        inner.statements = Some(Vec::new());
    }

    fn add_statement(&mut self, statement: vir_low::Statement) {
        let inner = self.inner();
        inner
            .statements
            .as_mut()
            .unwrap()
            .push(statement.set_default_position(inner.position));
    }

    fn discriminant(
        &mut self,
        snapshot: &vir_low::VariableDecl,
    ) -> SpannedEncodingResult<Option<vir_low::Expression>> {
        let inner = self.inner();
        if inner.ty.has_variants() {
            Ok(Some(inner.lowerer.obtain_enum_discriminant(
                snapshot.clone().into(),
                inner.ty,
                inner.position,
            )?))
        } else {
            Ok(None)
        }
    }

    fn add_join_memory_block_call(
        &mut self,
        _place: &vir_low::VariableDecl,
        address: &vir_low::VariableDecl,
        // root_address: &vir_low::VariableDecl,
        snapshot: &vir_low::VariableDecl,
    ) -> SpannedEncodingResult<()> {
        let inner = self.inner();
        inner.lowerer.encode_memory_block_join_method(inner.ty)?;
        // let address = inner.compute_address(place, root_address);
        let discriminant_call = inner.discriminant(snapshot)?;
        let mut builder = BuiltinMethodCallBuilder::new(
            inner.lowerer,
            CallContext::BuiltinMethod,
            "memory_block_join",
            inner.ty,
            inner.type_decl,
            inner.position,
        )?;
        builder.add_argument(address.clone().into());
        builder.add_full_permission_argument();
        if let Some(discriminant_call) = discriminant_call {
            builder.add_argument(discriminant_call);
        }
        let statement = builder.build();
        self.add_statement(statement);
        Ok(())
    }
}
