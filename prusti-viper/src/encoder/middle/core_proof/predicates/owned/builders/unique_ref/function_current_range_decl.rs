use crate::encoder::{
    errors::SpannedEncodingResult,
    middle::core_proof::{
        builtin_methods::CallContext,
        lifetimes::LifetimesInterface,
        lowerer::Lowerer,
        permissions::PermissionsInterface,
        places::PlacesInterface,
        predicates::{
            owned::builders::common::function_decl::FunctionDeclBuilder, PredicatesOwnedInterface,
        },
        snapshots::{IntoPureSnapshot, IntoSnapshot},
        type_layouts::TypeLayoutsInterface,
    },
};
use vir_crate::{
    common::identifier::WithIdentifier,
    low::{self as vir_low},
    middle::{self as vir_mid},
};

// FIXME: Code duplication with FracRefRangeSnapFunctionBuilder
pub(in super::super::super) struct UniqueRefCurrentRangeSnapFunctionBuilder<'l, 'p, 'v, 'tcx> {
    inner: FunctionDeclBuilder<'l, 'p, 'v, 'tcx>,
    address: vir_low::VariableDecl,
    start_index: vir_low::VariableDecl,
    end_index: vir_low::VariableDecl,
    reference_lifetime: vir_low::VariableDecl,
    slice_len: Option<vir_mid::VariableDecl>,
    pres: Vec<vir_low::Expression>,
    posts: Vec<vir_low::Expression>,
}

impl<'l, 'p, 'v, 'tcx> UniqueRefCurrentRangeSnapFunctionBuilder<'l, 'p, 'v, 'tcx> {
    pub(in super::super::super) fn new(
        lowerer: &'l mut Lowerer<'p, 'v, 'tcx>,
        ty: &'l vir_mid::Type,
        type_decl: &'l vir_mid::TypeDecl,
    ) -> SpannedEncodingResult<Self> {
        let slice_len = if ty.is_slice() {
            Some(vir_mid::VariableDecl::new(
                "slice_len",
                lowerer.size_type_mid()?,
            ))
        } else {
            None
        };
        Ok(Self {
            address: vir_low::VariableDecl::new("address", ty.to_snapshot(lowerer)?),
            start_index: vir_low::VariableDecl::new("start_index", lowerer.size_type()?),
            end_index: vir_low::VariableDecl::new("end_index", lowerer.size_type()?),
            reference_lifetime: vir_low::VariableDecl::new("lifetime", lowerer.lifetime_type()?),
            slice_len,
            inner: FunctionDeclBuilder::new(
                lowerer,
                "snap_unique_ref_current_range_aliased",
                ty,
                type_decl,
                Default::default(),
            )?,
            pres: Vec::new(),
            posts: Vec::new(),
        })
    }

    pub(in super::super::super) fn build(mut self) -> SpannedEncodingResult<vir_low::FunctionDecl> {
        let return_type = self.inner.range_result_type()?;
        let function = vir_low::FunctionDecl {
            name: format!(
                "{}${}",
                self.inner.function_name,
                self.inner.ty.get_identifier()
            ),
            kind: vir_low::FunctionKind::SnapRange,
            parameters: self.inner.parameters,
            body: None,
            pres: self.pres,
            posts: self.posts,
            return_type,
        };
        Ok(function)
    }

    pub(in super::super::super) fn create_parameters(&mut self) -> SpannedEncodingResult<()> {
        self.inner.parameters.push(self.address.clone());
        self.inner.parameters.push(self.start_index.clone());
        self.inner.parameters.push(self.end_index.clone());
        self.inner.parameters.push(self.reference_lifetime.clone());
        self.inner.create_lifetime_parameters()?;
        if let Some(slice_len_mid) = &self.slice_len {
            let slice_len = slice_len_mid.to_pure_snapshot(self.inner.lowerer)?;
            self.inner.parameters.push(slice_len);
        }
        self.inner.create_const_parameters()?;
        Ok(())
    }

    pub(in super::super::super) fn add_owned_precondition(&mut self) -> SpannedEncodingResult<()> {
        let wildcard_permission = self.inner.lowerer.wildcard_permission()?;
        let predicates = self.inner.lowerer.unique_ref_range(
            CallContext::BuiltinMethod,
            self.inner.ty,
            self.inner.type_decl,
            self.address.clone().into(),
            self.start_index.clone().into(),
            self.end_index.clone().into(),
            self.reference_lifetime.clone().into(),
            Some(wildcard_permission),
            self.inner.position,
        )?;
        self.pres.push(predicates);
        Ok(())
    }

    pub(in super::super::super) fn add_postcondition(&mut self) -> SpannedEncodingResult<()> {
        self.inner.create_range_postcondition(
            &mut self.posts,
            &self.address,
            &self.start_index,
            &self.end_index,
            |lowerer, ty, element_address, position| {
                let element_place = lowerer.place_option_none_constructor(position)?;
                let TODO_target_slice_len = None;
                lowerer.unique_ref_snap(
                    CallContext::BuiltinMethod,
                    ty,
                    ty,
                    element_place,
                    element_address,
                    self.reference_lifetime.clone().into(),
                    TODO_target_slice_len,
                    false,
                    position,
                )
            },
        )?;
        Ok(())
    }
}
