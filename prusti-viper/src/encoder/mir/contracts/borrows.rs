// © 2019, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use crate::{
    encoder::errors::{EncodingError, EncodingResult},
    utils::type_visitor::{self, TypeVisitor},
};
use prusti_rustc_interface::{
    abi::FieldIdx,
    hir::{self as hir, Mutability},
    middle::{
        mir,
        ty::{self, Ty, TyCtxt, TyKind},
    },
};
use std::fmt;

#[derive(Clone, Debug)]
pub struct BorrowInfo<P>
where
    P: fmt::Debug,
{
    /// Region of this borrow. None means static.
    pub region: Option<ty::BoundRegionKind>,
    pub blocking_paths: Vec<(P, Mutability)>,
    pub blocked_paths: Vec<(P, Mutability)>,
    //blocked_lifetimes: Vec<String>, TODO: Get this info from the constraints graph.
}

impl<P: fmt::Debug> BorrowInfo<P> {
    fn new(region: Option<ty::BoundRegionKind>) -> Self {
        BorrowInfo {
            region,
            blocking_paths: vec![],
            blocked_paths: vec![],
        }
    }
}

impl<P: fmt::Debug> fmt::Display for BorrowInfo<P> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let lifetime = match self.region {
            None => "static".to_string(),
            Some(ty::BoundRegionKind::BrAnon(_)) => "anon".to_string(),
            Some(ty::BoundRegionKind::BrNamed(_, name)) => name.to_string(),
            _ => unimplemented!(),
        };
        writeln!(f, "BorrowInfo<{lifetime}> {{")?;
        for path in self.blocking_paths.iter() {
            writeln!(f, "  {path:?}")?;
        }
        writeln!(f, "  --*")?;
        for path in self.blocked_paths.iter() {
            writeln!(f, "  {path:?}")?;
        }
        writeln!(f, "}}")
    }
}

pub(super) struct BorrowInfoCollectingVisitor<'tcx> {
    pub(super) borrow_infos: Vec<BorrowInfo<mir::Place<'tcx>>>,
    /// References that were passed as arguments. We are interested only in
    /// references that can be blocked.
    pub(super) references_in: Vec<(mir::Place<'tcx>, Mutability)>,
    tcx: TyCtxt<'tcx>,
    /// Can the currently analysed path block other paths? For return
    /// type this is initially true, and for parameters it is true below
    /// the first reference.
    is_path_blocking: bool,
    current_path: Option<mir::Place<'tcx>>,
}

impl<'tcx> BorrowInfoCollectingVisitor<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>) -> Self {
        BorrowInfoCollectingVisitor {
            borrow_infos: vec![],
            references_in: vec![],
            tcx,
            is_path_blocking: false,
            current_path: None,
        }
    }

    pub fn analyse_return_ty(&mut self, ty: Ty<'tcx>) -> EncodingResult<()> {
        self.is_path_blocking = true;
        self.current_path = Some(mir::RETURN_PLACE.into());
        self.visit_ty(ty)?;
        self.current_path = None;
        Ok(())
    }

    pub fn analyse_arg(&mut self, arg: mir::Local, ty: Ty<'tcx>) -> EncodingResult<()> {
        self.is_path_blocking = false;
        self.current_path = Some(arg.into());
        self.visit_ty(ty)?;
        self.current_path = None;
        Ok(())
    }

    pub fn extract_bound_region(&self, region: ty::Region<'tcx>) -> Option<ty::BoundRegionKind> {
        match region.kind() {
            ty::RegionKind::ReFree(free_region) => Some(free_region.bound_region),
            // TODO: is this correct?!
            ty::RegionKind::ReLateBound(_, bound_region) => Some(bound_region.kind),
            ty::RegionKind::ReEarlyBound(early_region) => Some(ty::BoundRegionKind::BrNamed(
                early_region.def_id,
                early_region.name,
            )),
            ty::RegionKind::ReStatic => None,
            ty::RegionKind::ReErased => None,
            ty::RegionKind::ReVar(_) => None,
            // &ty::RegionKind::ReScope(_scope) => None,
            x => unimplemented!("{:?}", x),
        }
    }

    pub fn get_or_create_borrow_info(
        &mut self,
        region: Option<ty::BoundRegionKind>,
    ) -> &mut BorrowInfo<mir::Place<'tcx>> {
        if let Some(index) = self
            .borrow_infos
            .iter()
            .position(|info| info.region == region)
        {
            &mut self.borrow_infos[index]
        } else {
            let borrow_info = BorrowInfo::new(region);
            self.borrow_infos.push(borrow_info);
            self.borrow_infos.last_mut().unwrap()
        }
    }
}

impl<'tcx> TypeVisitor<'tcx> for BorrowInfoCollectingVisitor<'tcx> {
    type Error = EncodingError;

    fn visit_unsupported_sty(&mut self, sty: &TyKind<'tcx>) -> Result<(), Self::Error> {
        Err(EncodingError::unsupported(format!(
            "unsupported type {sty:?}",
        )))
    }

    fn tcx(&self) -> TyCtxt<'tcx> {
        self.tcx
    }

    fn unsupported<S: ToString>(&self, msg: S) -> Self::Error {
        EncodingError::unsupported(msg.to_string())
    }

    #[tracing::instrument(level = "trace", skip(self))]
    fn visit_adt_variant(
        &mut self,
        adt: ty::AdtDef<'tcx>,
        idx: prusti_rustc_interface::target::abi::VariantIdx,
        variant: &ty::VariantDef,
        substs: ty::GenericArgsRef<'tcx>,
    ) -> Result<(), Self::Error> {
        let old_path = self.current_path.take().unwrap();
        self.current_path = Some(self.tcx.mk_place_downcast(old_path, adt, idx));
        type_visitor::walk_adt_variant(self, variant, substs)?;
        self.current_path = Some(old_path);
        Ok(())
    }

    #[tracing::instrument(level = "trace", skip(self))]
    fn visit_field(
        &mut self,
        index: usize,
        field: &ty::FieldDef,
        substs: ty::GenericArgsRef<'tcx>,
    ) -> Result<(), Self::Error> {
        let old_path = self.current_path.take().unwrap();
        let ty = field.ty(self.tcx(), substs);
        let field_id = FieldIdx::from_usize(index);
        let new_path = self.tcx.mk_place_field(old_path, field_id, ty);
        self.current_path = Some(new_path);
        // self.current_path = Some(old_path.clone().field(field_id, ty));
        type_visitor::walk_field(self, field, substs)?;
        self.current_path = Some(old_path);
        Ok(())
    }

    #[tracing::instrument(level = "trace", skip(self), fields(current_path = ?self.current_path))]
    fn visit_ref(
        &mut self,
        region: ty::Region<'tcx>,
        ty: ty::Ty<'tcx>,
        mutability: hir::Mutability,
    ) -> Result<(), Self::Error> {
        let bound_region = self.extract_bound_region(region);
        let is_path_blocking = self.is_path_blocking;
        let old_path = self.current_path.take().unwrap();
        let current_path = self.tcx.mk_place_deref(old_path);
        self.current_path = Some(current_path);
        let borrow_info = self.get_or_create_borrow_info(bound_region);
        if is_path_blocking {
            borrow_info.blocking_paths.push((current_path, mutability));
        } else {
            borrow_info.blocked_paths.push((current_path, mutability));
            self.references_in.push((current_path, mutability));
        }
        self.is_path_blocking = true;
        //type_visitor::walk_ref(self, region, ty, mutability)?;
        self.is_path_blocking = is_path_blocking;
        self.current_path = Some(old_path);
        Ok(())
    }

    fn visit_tuple(&mut self, types: &'tcx ty::List<ty::Ty<'tcx>>) -> Result<(), Self::Error> {
        let old_path = self.current_path.take().unwrap();
        for (i, ty) in types.into_iter().enumerate() {
            let field = FieldIdx::from_usize(i);
            self.current_path = Some(self.tcx().mk_place_field(old_path, field, ty));
            self.visit_ty(ty)?;
        }
        self.current_path = Some(old_path);
        Ok(())
    }

    #[tracing::instrument(level = "trace", skip(self), fields(current_path = ?self.current_path))]
    fn visit_raw_ptr(
        &mut self,
        ty: ty::Ty<'tcx>,
        mutability: hir::Mutability,
    ) -> Result<(), Self::Error> {
        // Do nothing.
        Ok(())
    }
}
