use prusti_rustc_interface::{
    hir::def_id::{CrateNum, LOCAL_CRATE},
    serialize::{Decodable, Encodable},
    span::DUMMY_SP,
};
use rustc_hash::FxHashMap;
use std::{fs, io, path};

use crate::{
    environment::{Environment, body::CrossCrateBodies},
    specs::typed::DefSpecificationMap, PrustiError,
};

use super::{encoder::DefSpecsEncoder, decoder::DefSpecsDecoder};

pub struct CrossCrateSpecs;

impl CrossCrateSpecs {
    pub fn import_export_cross_crate(
        env: &mut Environment,
        def_spec: &mut DefSpecificationMap,
        dir: &path::PathBuf,
    ) {
        Self::export_specs(env, def_spec, dir);
        Self::import_specs(env, def_spec, dir);
    }

    fn export_specs(env: &Environment, def_spec: &DefSpecificationMap, dir: &path::PathBuf) {
        let target_filename = Self::get_crate_specs_path(env, dir, LOCAL_CRATE);
        if let Err(e) = Self::write_into_file(env, &def_spec, &target_filename) {
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

    fn get_crate_specs_path(env: &Environment, dir: &path::PathBuf, crate_num: CrateNum) -> path::PathBuf {
        let mut path = dir.join("serialized_specs");
        if env.name.crate_name(crate_num) == "prusti_contracts_core" {
            println!("prusti-contracts-core stable crate id is: {:x}\n", env.tcx().stable_crate_id(crate_num).to_u64());
        }
        path.push(format!(
            "{}-{:x}.bin",
            env.name.crate_name(crate_num),
            env.tcx().stable_crate_id(crate_num).to_u64(),
        ));
        path
    }

    fn import_specs(
        env: &mut Environment,
        def_spec: &mut DefSpecificationMap,
        dir: &path::PathBuf,
    ) {
        // TODO: atm one needs to write `extern crate extern_spec_lib` to import the specs
        // from a crate which is not used in the current crate (e.g. an `#[extern_spec]` only crate)
        // Otherwise the crate doesn't show up in `tcx.crates()`.  Is there some better way
        // to get dependency crates, which doesn't ignore unused ones? Maybe:
        // https://doc.rust-lang.org/stable/nightly-rustc/rustc_metadata/creader/struct.CrateMetadataRef.html#method.dependencies
        for crate_num in env.tcx().crates(()) {
            if *crate_num == LOCAL_CRATE {
                continue;
            }

            let file = Self::get_crate_specs_path(env, &dir, *crate_num);
            // println!("Check file: {:?}", file);
            if file.is_file() {
                if let Err(e) = Self::import_from_file(env, def_spec, &file) {
                    PrustiError::internal(
                        format!(
                            "error importing specs from file \"{}\": {}",
                            file.to_string_lossy(),
                            e
                        ),
                        DUMMY_SP.into(),
                    )
                    .emit(&env.diagnostic);
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

        fs::create_dir_all(path.parent().unwrap())?;
        let mut file = fs::File::create(path)?;
        file.write(&encoder.into_inner())
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
        let mut decoder = DefSpecsDecoder::new(env.tcx(), &data);

        let proc_specs = FxHashMap::decode(&mut decoder);
        let type_specs = FxHashMap::decode(&mut decoder);
        let mirs_of_specs = CrossCrateBodies::decode(&mut decoder);
        def_spec.import_external(proc_specs, type_specs, env);
        env.body.import_external_bodies(mirs_of_specs);
        Ok(())
    }
}
