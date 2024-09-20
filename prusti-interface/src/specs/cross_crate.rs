use prusti_rustc_interface::{
    metadata::creader::CStore,
    serialize::{Decodable, Encodable},
    session::config::OutputType,
    span::DUMMY_SP,
};
use rustc_hash::FxHashMap;
use std::{fs, io, path};

use crate::{
    environment::{body::CrossCrateBodies, Environment},
    specs::typed::DefSpecificationMap,
    PrustiError,
};

use super::{decoder::DefSpecsDecoder, encoder::DefSpecsEncoder};

pub struct CrossCrateSpecs;

impl CrossCrateSpecs {
    pub fn import_export_cross_crate(env: &mut Environment, def_spec: &mut DefSpecificationMap) {
        Self::export_specs(env, def_spec);
        Self::import_specs(env, def_spec);
    }

    fn export_specs(env: &Environment, def_spec: &DefSpecificationMap) {
        let outputs = env.tcx().output_filenames(());

        let metadata_filename = outputs.path(OutputType::Metadata);
        let target_filename = metadata_filename.as_path().to_owned();
        let target_filename = target_filename.with_extension("specs");

        if let Err(e) = Self::write_into_file(env, def_spec, &target_filename) {
            PrustiError::internal(
                format!(
                    "error exporting specs to file \"{}\": {}",
                    target_filename.to_string_lossy(),
                    e
                ),
                DUMMY_SP.into(),
            )
            .emit(&env.diagnostic);
        }
    }

    fn import_specs(env: &mut Environment, def_spec: &mut DefSpecificationMap) {
        let cstore = CStore::from_tcx(env.tcx());
        // TODO: atm one needs to write `extern crate extern_spec_lib` to import the specs
        // from a crate which is not used in the current crate (e.g. an `#[extern_spec]` only crate)
        // Otherwise the crate doesn't show up in `tcx.crates()`.  Is there some better way
        // to get dependency crates, which doesn't ignore unused ones? Maybe:
        // https://doc.rust-lang.org/stable/nightly-rustc/rustc_metadata/creader/struct.CrateMetadataRef.html#method.dependencies
        for crate_num in env.tcx().crates(()) {
            if let Some(extern_crate) = env.tcx().extern_crate(*crate_num) {
                if extern_crate.is_direct() {
                    let cs = env.tcx().used_crate_source(*crate_num);
                    let mut source = cs.paths().next().unwrap().clone();
                    source.set_extension("specs");
                    if source.is_file() {
                        if let Err(e) = Self::import_from_file(env, def_spec, &source) {
                            PrustiError::internal(
                                format!(
                                    "error importing specs from file \"{}\": {}",
                                    source.to_string_lossy(),
                                    e
                                ),
                                DUMMY_SP.into(),
                            )
                            .emit(&env.diagnostic);
                        }
                    }
                }
            }
        }
    }

    fn write_into_file(
        env: &Environment,
        def_spec: &DefSpecificationMap,
        path: &path::PathBuf,
    ) -> io::Result<()> {
        DefSpecsEncoder::serialize(
            env.tcx(),
            &path,
            (
                &def_spec.proc_specs,
                &def_spec.type_specs,
                CrossCrateBodies::from(&env.body),
            ),
        )
    }

    fn import_from_file(
        env: &mut Environment,
        def_spec: &mut DefSpecificationMap,
        path: &path::PathBuf,
    ) -> io::Result<()> {
        use std::io::Read;
        let mut data = Vec::new();
        let mut file = fs::File::open(path)?;
        file.read_to_end(&mut data)?;
        let mut decoder = DefSpecsDecoder::new(env.tcx(), &data)?;

        let proc_specs = FxHashMap::decode(&mut decoder);
        let type_specs = FxHashMap::decode(&mut decoder);
        let mirs_of_specs = CrossCrateBodies::decode(&mut decoder);
        def_spec.import_external(proc_specs, type_specs, env);
        env.body.import_external_bodies(mirs_of_specs);
        Ok(())
    }
}
