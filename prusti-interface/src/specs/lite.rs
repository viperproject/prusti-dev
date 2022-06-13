use std::collections::HashMap;
use std::fs::File;
use std::io;
use std::io::{Write};
use std::path::Path;
use std::rc::Rc;

use log::warn;

use prusti_rustc_interface::hir::def_id::DefId;
use prusti_rustc_interface::macros::{TyDecodable, TyEncodable};
use prusti_rustc_interface::middle::mir;
use prusti_rustc_interface::middle::ty::TyCtxt;
use rustc_serialize::{Decodable, Encodable};

use crate::specs::typed::{
    DefSpecificationMap, ProcedureSpecification, PrustiAssertion, PrustiAssumption,
    SpecGraph, TypeSpecification,
};

use super::{
    decoder::{DefSpecsBlob, DefSpecsDecoder},
    encoder::DefSpecsEncoder,
};

/// A subset of [DefSpecificationMap]. Used for serialization of
/// specification data (of the currently compiled crate), loaded by dependent crates
/// that import external specification (from the current crate).
#[derive(TyEncodable)]
pub struct DefSpecificationMapLite<'tcx, 'a> {
    proc_specs: &'a HashMap<DefId, SpecGraph<ProcedureSpecification>>,
    type_specs: &'a HashMap<DefId, TypeSpecification>,
    prusti_assertions: &'a HashMap<DefId, PrustiAssertion>,
    prusti_assumptions: &'a HashMap<DefId, PrustiAssumption>,

    local_mirs: &'a HashMap<DefId, Rc<mir::Body<'tcx>>>,
}

impl<'tcx, 'a> DefSpecificationMapLite<'tcx, 'a> {
    pub(crate) fn from_def_spec(def_spec: &'a DefSpecificationMap<'tcx>) -> Self {
        Self {
            proc_specs: &def_spec.proc_specs,
            type_specs: &def_spec.type_specs,
            prusti_assertions: &def_spec.prusti_assertions,
            prusti_assumptions: &def_spec.prusti_assumptions,

            local_mirs: &def_spec.local_mirs,
        }
    }

    pub(crate) fn write_into_file(self, tcx: TyCtxt<'tcx>, path: &Path) -> Result<(), io::Error> {
        let mut encoder = DefSpecsEncoder::new(tcx);
        self.encode(&mut encoder);

        std::fs::create_dir_all(path.parent().unwrap()).unwrap();
        File::create(path).and_then(|mut file| file.write(&encoder.into_inner())).map_err(|err| {
            warn!("could not encode metadata for crate `{:?}`, error: {:?}", "LOCAL_CRATE", err);
            err
        })?;
        Ok(())
    }
}

#[derive(TyDecodable)]
pub struct DefSpecificationMapLiteOwned<'tcx> {
    proc_specs: HashMap<DefId, SpecGraph<ProcedureSpecification>>,
    type_specs: HashMap<DefId, TypeSpecification>,
    prusti_assertions: HashMap<DefId, PrustiAssertion>,
    prusti_assumptions: HashMap<DefId, PrustiAssumption>,

    local_mirs: HashMap<DefId, Rc<mir::Body<'tcx>>>,
}

impl<'tcx> DefSpecificationMapLiteOwned<'tcx> {
    pub(crate) fn read_from_file(tcx: TyCtxt<'tcx>, path: &Path) -> io::Result<Self> {
        DefSpecsBlob::from_file(path).and_then(|blob| {
            let mut decoder = DefSpecsDecoder::new(tcx, &blob);
            Ok(Self::decode(&mut decoder))
        })
    }

    pub(crate) fn extend(self, def_spec: &mut DefSpecificationMap<'tcx>) {
        def_spec.proc_specs.extend(self.proc_specs);
        def_spec.type_specs.extend(self.type_specs);
        def_spec.prusti_assertions.extend(self.prusti_assertions);
        def_spec.prusti_assumptions.extend(self.prusti_assumptions);

        def_spec.local_mirs.extend(self.local_mirs);
    }
}
