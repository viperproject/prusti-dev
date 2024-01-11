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

// FIXME: Code duplication with UniqueRefCurrentRangeSnapFunctionBuilder
pub(in super::super::super) struct FracRefRangeSnapFunctionBuilder<'l, 'p, 'v, 'tcx> {
    inner: FunctionDeclBuilder<'l, 'p, 'v, 'tcx>,
    address: vir_low::VariableDecl,
    start_index: vir_low::VariableDecl,
    end_index: vir_low::VariableDecl,
    reference_lifetime: vir_low::VariableDecl,
    slice_len: Option<vir_mid::VariableDecl>,
    pres: Vec<vir_low::Expression>,
    posts: Vec<vir_low::Expression>,
}

impl<'l, 'p, 'v, 'tcx> FracRefRangeSnapFunctionBuilder<'l, 'p, 'v, 'tcx> {
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
                "snap_frac_ref_range_aliased",
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

    // fn result_type(&mut self) -> SpannedEncodingResult<vir_low::Type> {
    //     let vir_mid::Type::Pointer(pointer_type) = self.inner.ty else {
    //         unreachable!("{} must be a pointer type", self.inner.ty);
    //     };
    //     let element_type = pointer_type.target_type.to_snapshot(self.inner.lowerer)?;
    //     let return_type = vir_low::Type::seq(element_type);
    //     Ok(return_type)
    // }

    // fn result(&mut self) -> SpannedEncodingResult<vir_low::VariableDecl> {
    //     Ok(vir_low::VariableDecl::result_variable(self.result_type()?))
    // }

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
        let predicates = self.inner.lowerer.frac_ref_range(
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
        // use vir_low::macros::*;
        // let size_type = self.inner.lowerer.size_type_mid()?;
        // var_decls! {
        //     index: Int
        // }
        // let vir_mid::Type::Pointer(ty) = self.inner.ty else {
        //     unreachable!()
        // };
        // let initial_address = self.inner.lowerer.pointer_address(
        //     self.inner.ty,
        //     self.address.clone().into(),
        //     self.inner.position,
        // )?;
        // let vir_mid::Type::Pointer(pointer_type) = self.inner.ty else {
        //     unreachable!()
        // };
        // let size = self
        //     .inner
        //     .lowerer
        //     .encode_type_size_expression2(&pointer_type.target_type, &*pointer_type.target_type)?;
        // let element_place = self
        //     .inner
        //     .lowerer
        //     .place_option_none_constructor(self.inner.position)?;
        // let element_address = self.inner.lowerer.address_offset(
        //     size,
        //     initial_address,
        //     index.clone().into(),
        //     self.inner.position,
        // )?;
        // let TODO_target_slice_len = None;
        // let snap_call = self.inner.lowerer.frac_ref_snap(
        //     CallContext::BuiltinMethod,
        //     &ty.target_type,
        //     &*ty.target_type,
        //     element_place,
        //     element_address.clone(),
        //     self.reference_lifetime.clone().into(),
        //     TODO_target_slice_len,
        //     self.inner.position,
        // )?;
        // let result_type = self.result_type()?;
        // let result = self.result()?;
        // let start_index = self.inner.lowerer.obtain_constant_value(
        //     &size_type,
        //     self.start_index.clone().into(),
        //     self.inner.position,
        // )?;
        // let end_index = self.inner.lowerer.obtain_constant_value(
        //     &size_type,
        //     self.end_index.clone().into(),
        //     self.inner.position,
        // )?;
        // let result_len = vir_low::Expression::container_op(
        //     vir_low::ContainerOpKind::SeqLen,
        //     result_type.clone(),
        //     vec![result.clone().into()],
        //     self.inner.position,
        // );
        // let index_diff = vir_low::Expression::subtract(end_index.clone(), start_index.clone());
        // self.posts.push(expr!([result_len] == [index_diff]));
        // let element_snap = vir_low::Expression::container_op(
        //     vir_low::ContainerOpKind::SeqIndex,
        //     result_type,
        //     vec![
        //         result.into(),
        //         vir_low::Expression::subtract(index.clone().into(), start_index.clone()),
        //     ],
        //     self.inner.position,
        // );
        // let body = expr!(
        //     (([start_index] <= index) && (index < [end_index])) ==>
        //     ([snap_call] == [element_snap])
        // );
        // let expression = vir_low::Expression::forall(
        //     vec![index],
        //     vec![vir_low::Trigger::new(vec![element_address])],
        //     body,
        // );
        // self.posts.push(expression);
        self.inner.create_range_postcondition(
            &mut self.posts,
            &self.address,
            &self.start_index,
            &self.end_index,
            |lowerer, ty, element_address, position| {
                let element_place = lowerer.place_option_none_constructor(position)?;
                let TODO_target_slice_len = None;
                lowerer.frac_ref_snap(
                    CallContext::BuiltinMethod,
                    ty,
                    ty,
                    element_place,
                    element_address,
                    self.reference_lifetime.clone().into(),
                    TODO_target_slice_len,
                    position,
                )
            },
        )?;
        Ok(())
    }
}
