use std::path::PathBuf;

use prusti_rustc_interface::{
    hir::def_id::{CrateNum, DefId, DefIndex, DefPathHash},
    middle::{
        implement_ty_decoder,
        ty::{codec::TyDecoder, Ty, TyCtxt},
    },
    serialize::{opaque, Decodable},
    session::StableCrateId,
    span::{source_map::StableSourceFileId, BytePos, Span, SyntaxContext},
};
use rustc_hash::FxHashMap;

pub struct DefSpecsDecoder<'a, 'tcx> {
    opaque: opaque::MemDecoder<'a>,
    tcx: TyCtxt<'tcx>,
    ty_rcache: FxHashMap<usize, Ty<'tcx>>,
    specs_file: PathBuf,
    crate_name: String,
}

impl<'a, 'tcx> DefSpecsDecoder<'a, 'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>, data: &'a [u8], specs_file: PathBuf, crate_name: &str) -> Self {
        DefSpecsDecoder {
            opaque: opaque::MemDecoder::new(data, 0),
            tcx,
            ty_rcache: Default::default(),
            specs_file,
            crate_name: crate_name.to_string(),
        }
    }

    fn def_path_hash_to_def_id(&self, hash: DefPathHash) -> DefId {
        // Sanity check
        let cstore = std::panic::AssertUnwindSafe(self.tcx.cstore_untracked());
        let result = std::panic::catch_unwind(|| {
            cstore.stable_crate_id_to_crate_num(hash.stable_crate_id())
        });
        if result.is_err() {
            // The way to fix this in Prusti is to somehow regenerate the `.specs`
            // file whenever the DefPathHash might change (e.g. different args)
            let (specs_file, crate_name) = (&self.specs_file, &self.crate_name);
            let target_dir = specs_file.parent().unwrap();
            panic!(
                "A compiled dependency (referenced from `{specs_file:?}`) is out of sync. \
            Running `cargo clean -p {crate_name}` and rebuilding should fix this. \
            Otherwise try deleting the entire `{target_dir:?}` directory."
            )
        }
        // Get `DefId`
        self.tcx.def_path_hash_to_def_id(hash, &mut || {
            panic!("DefPathHash not found in the local crate")
        })
    }
}

// This impl makes sure that we get a runtime error when we try decode a
// `DefIndex` that is not contained in a `DefId`. Such a case would be problematic
// because we would not know how to transform the `DefIndex` to the current
// context.
impl<'a, 'tcx> Decodable<DefSpecsDecoder<'a, 'tcx>> for DefIndex {
    fn decode(_: &mut DefSpecsDecoder<'a, 'tcx>) -> DefIndex {
        panic!("trying to decode `DefIndex` outside the context of a `DefId`")
    }
}

// Both the `CrateNum` and the `DefIndex` of a `DefId` can change in between two
// compilation sessions. We use the `DefPathHash`, which is stable across
// sessions, to map the old `DefId` to the new one.
impl<'a, 'tcx> Decodable<DefSpecsDecoder<'a, 'tcx>> for DefId {
    fn decode(d: &mut DefSpecsDecoder<'a, 'tcx>) -> Self {
        let def_path_hash = DefPathHash::decode(d);
        d.def_path_hash_to_def_id(def_path_hash)
    }
}

impl<'a, 'tcx> Decodable<DefSpecsDecoder<'a, 'tcx>> for CrateNum {
    fn decode(d: &mut DefSpecsDecoder<'a, 'tcx>) -> CrateNum {
        let stable_id = StableCrateId::decode(d);
        d.tcx.stable_crate_id_to_crate_num(stable_id)
    }
}

// See https://doc.rust-lang.org/nightly/nightly-rustc/rustc_metadata/rmeta/decoder/struct.DecodeContext.html
impl<'a, 'tcx> Decodable<DefSpecsDecoder<'a, 'tcx>> for Span {
    fn decode(s: &mut DefSpecsDecoder<'a, 'tcx>) -> Span {
        let sm = s.tcx.sess.source_map();
        let pos = [(); 2].map(|_| {
            let ssfi = StableSourceFileId::decode(s);
            let rel_bp = BytePos::decode(s);
            sm.source_file_by_stable_id(ssfi)
                // See comment in 'encoder.rs'
                .map(|sf| sf.start_pos + rel_bp)
                // This should hopefully never fail,
                // so maybe could be an `unwrap` instead?
                .unwrap_or(BytePos(0))
        });
        Span::new(pos[0], pos[1], SyntaxContext::root(), None)
    }
}

implement_ty_decoder!(DefSpecsDecoder<'a, 'tcx>);

impl<'a, 'tcx> TyDecoder for DefSpecsDecoder<'a, 'tcx> {
    type I = TyCtxt<'tcx>;
    const CLEAR_CROSS_CRATE: bool = true;

    fn interner(&self) -> Self::I {
        self.tcx
    }

    fn cached_ty_for_shorthand<F>(&mut self, shorthand: usize, or_insert_with: F) -> Ty<'tcx>
    where
        F: FnOnce(&mut Self) -> Ty<'tcx>,
    {
        if let Some(&ty) = self.ty_rcache.get(&shorthand) {
            return ty;
        }

        let ty = or_insert_with(self);
        self.ty_rcache.insert(shorthand, ty);
        ty
    }

    fn with_position<F, R>(&mut self, pos: usize, f: F) -> R
    where
        F: FnOnce(&mut Self) -> R,
    {
        let new_opaque = opaque::MemDecoder::new(self.opaque.data(), pos);
        let old_opaque = std::mem::replace(&mut self.opaque, new_opaque);
        let r = f(self);
        self.opaque = old_opaque;
        r
    }

    fn decode_alloc_id(&mut self) -> rustc_middle::mir::interpret::AllocId {
        unimplemented!("decode_alloc_id")
    }
}
