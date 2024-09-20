use std::io;

use prusti_rustc_interface::{
    hir::def_id::{CrateNum, DefId, DefIndex, DefPathHash},
    middle::{
        implement_ty_decoder,
        ty::{codec::TyDecoder, Ty, TyCtxt},
    },
    ast::AttrId,
    serialize::{opaque, Decodable, Decoder},
    session::StableCrateId,
    span::{BytePos, ExpnId, Symbol, Span, SpanDecoder, StableSourceFileId, SyntaxContext},
};
use rustc_hash::FxHashMap;

pub struct DefSpecsDecoder<'a, 'tcx> {
    opaque: opaque::MemDecoder<'a>,
    tcx: TyCtxt<'tcx>,
    ty_rcache: FxHashMap<usize, Ty<'tcx>>,
}

impl<'a, 'tcx> DefSpecsDecoder<'a, 'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>, data: &'a [u8]) -> io::Result<Self> {
        Ok(DefSpecsDecoder {
            opaque: opaque::MemDecoder::new(data, 0).unwrap(),
            tcx,
            ty_rcache: Default::default(),
        })
    }
}

//TODO: Unify with Encoder
// Tags used for encoding Spans:
const TAG_FULL_SPAN: u8 = 0;
const TAG_PARTIAL_SPAN: u8 = 1;

// Tags for encoding Symbol's
const SYMBOL_STR: u8 = 0;
const SYMBOL_OFFSET: u8 = 1;
const SYMBOL_PREINTERNED: u8 = 2;

impl<'a, 'tcx> SpanDecoder for DefSpecsDecoder<'a, 'tcx> {
    fn decode_span(&mut self) -> Span {
        let sm = self.tcx.sess.source_map();
        let pos = [(); 2].map(|_| {
            let ssfi = StableSourceFileId::decode(self);
            let rel_bp = BytePos::decode(self);
            sm.source_file_by_stable_id(ssfi)
                // See comment in 'encoder.rs'
                .map(|sf| sf.start_pos + rel_bp)
                // This should hopefully never fail,
                // so maybe could be an `unwrap` instead?
                .unwrap_or(BytePos(0))
        });
        Span::new(pos[0], pos[1], SyntaxContext::root(), None)
    }

    fn decode_symbol(&mut self) -> Symbol {
        let tag = self.read_u8();

        match tag {
            SYMBOL_STR => {
                let s = self.read_str();
                Symbol::intern(s)
            }
            SYMBOL_OFFSET => {
                // read str offset
                let pos = self.read_usize();

                // move to str ofset and read
                let sym = self.opaque.with_position(pos, |d| {
                    let s = d.read_str();
                    Symbol::intern(s)
                });
                sym
            }
            SYMBOL_PREINTERNED => {
                let symbol_index = self.read_u32();
                Symbol::new_from_decoded(symbol_index)
            }
            _ => unreachable!(),
        }
    }

    fn decode_expn_id(&mut self) -> ExpnId {
        todo!()
    }

    fn decode_syntax_context(&mut self) -> SyntaxContext {
        todo!()
    }

    fn decode_crate_num(&mut self) -> CrateNum {
        let stable_id = StableCrateId::decode(self);
        self.tcx.stable_crate_id_to_crate_num(stable_id)
    }
    fn decode_def_index(&mut self) -> DefIndex {
        panic!("trying to decode `DefIndex` outside the context of a `DefId`")
    }

    // Both the `CrateNum` and the `DefIndex` of a `DefId` can change in between two
    // compilation sessions. We use the `DefPathHash`, which is stable across
    // sessions, to map the old `DefId` to the new one.
    fn decode_def_id(&mut self) -> DefId {
        let def_path_hash = DefPathHash::decode(self);
        self.tcx
            .def_path_hash_to_def_id(def_path_hash).unwrap()
    }

    fn decode_attr_id(&mut self) -> AttrId {
        todo!()
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
        let new_opaque = self.opaque.split_at(pos);
        let old_opaque = std::mem::replace(&mut self.opaque, new_opaque);
        let r = f(self);
        self.opaque = old_opaque;
        r
    }

    fn decode_alloc_id(&mut self) -> rustc_middle::mir::interpret::AllocId {
        unimplemented!("decode_alloc_id")
    }
}
