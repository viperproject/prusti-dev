use prusti_rustc_interface::{
    serialize::{Decodable, Encodable},
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
    #[tracing::instrument(level = "debug", skip_all)]
    pub fn import_export_cross_crate(env: &mut Environment, def_spec: &mut DefSpecificationMap) {
        Self::export_specs(env, def_spec);
        Self::import_specs(env, def_spec);
    }

    #[tracing::instrument(level = "debug", skip_all)]
    fn export_specs(env: &Environment, def_spec: &DefSpecificationMap) {
        let outputs = env.tcx().output_filenames(());
        // If we run `rustc` without the `--out-dir` flag set, then don't export specs
        if outputs.out_directory.to_string_lossy() == "" {
            return;
        }
        let target_filename = outputs
            .out_directory
            .join(format!("lib{}.specs", env.name.local_crate_filename()));
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

    #[tracing::instrument(level = "debug", skip_all)]
    fn import_specs(env: &mut Environment, def_spec: &mut DefSpecificationMap) {
        // TODO: atm one needs to write `extern crate extern_spec_lib` to import the specs
        // from a crate which is not used in the current crate (e.g. an `#[extern_spec]` only crate)
        // Otherwise the crate doesn't show up in `tcx.crates()`.  Is there some better way
        // to get dependency crates, which doesn't ignore unused ones? Maybe:
        // https://doc.rust-lang.org/stable/nightly-rustc/rustc_metadata/creader/struct.CrateMetadataRef.html#method.dependencies
        for crate_num in env.tcx().crates(()) {
            if let Some(extern_crate) = env.tcx().extern_crate(crate_num.as_def_id()) {
                if extern_crate.is_direct() {
                    let crate_name = env.tcx().crate_name(*crate_num);
                    let crate_source = env.tcx().used_crate_source(*crate_num);
                    let mut source = crate_source.paths().next().unwrap().clone();
                    source.set_extension("specs");
                    if source.is_file() {
                        if let Err(e) =
                            Self::import_from_file(env, def_spec, &source, crate_name.as_str())
                        {
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
    ) -> io::Result<usize> {
        use std::io::Write;
        let mut encoder = DefSpecsEncoder::new(env.tcx());
        def_spec.proc_specs.encode(&mut encoder);
        def_spec.type_specs.encode(&mut encoder);
        CrossCrateBodies::from(&env.body).encode(&mut encoder);

        // Probably not needed; dir should already exist?
        fs::create_dir_all(path.parent().unwrap())?;
        let mut file = fs::File::create(path)?;
        file.write(&encoder.into_inner())
    }

    #[tracing::instrument(level = "debug", skip(env, def_spec))]
    fn import_from_file(
        env: &mut Environment,
        def_spec: &mut DefSpecificationMap,
        path: &path::PathBuf,
        crate_name: &str,
    ) -> io::Result<()> {
        use std::io::Read;
        let mut data = Vec::new();
        let mut file = fs::File::open(path)?;
        file.read_to_end(&mut data)?;
        let mut decoder = DefSpecsDecoder::new(env.tcx(), &data, path.clone(), crate_name);

        let proc_specs = FxHashMap::decode(&mut decoder);
        let type_specs = FxHashMap::decode(&mut decoder);
        let mirs_of_specs = CrossCrateBodies::decode(&mut decoder);
        def_spec.import_external(proc_specs, type_specs, env);
        env.body.import_external_bodies(mirs_of_specs);
        Ok(())
    }
}
