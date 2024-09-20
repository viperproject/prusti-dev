use std::{
    collections::hash_map::Entry, io::{self, Error}, path::{Path, PathBuf}
};

use prusti_rustc_interface::{
    data_structures::fx::{FxHashMap, FxIndexSet},
    hir::def_id::{CrateNum, DefId, DefIndex, LOCAL_CRATE},
    middle::{
        mir::interpret::AllocId,
        ty::{self, codec::TyEncoder, PredicateKind, Ty, TyCtxt},
    },
    serialize::{opaque, Encodable, Encoder},
    span::{
        hygiene::{raw_encode_syntax_context, HygieneEncodeContext},
        ExpnId, SourceFile, Span, SpanEncoder, StableSourceFileId, Symbol, SyntaxContext,
    },
};

// Tags for encoding Symbol's
const SYMBOL_STR: u8 = 0;
const SYMBOL_OFFSET: u8 = 1;
const SYMBOL_PREINTERNED: u8 = 2;

pub struct DefSpecsEncoder<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    opaque: opaque::FileEncoder,
    type_shorthands: FxHashMap<Ty<'tcx>, usize>,
    predicate_shorthands: FxHashMap<PredicateKind<'tcx>, usize>,
    interpret_allocs: FxIndexSet<AllocId>,
    hygiene_context: &'a HygieneEncodeContext,
        symbol_table: FxHashMap<Symbol, usize>,

}

impl<'a, 'tcx> DefSpecsEncoder<'a, 'tcx> {
    pub fn serialize<T: for<'b> Encodable<DefSpecsEncoder<'b, 'tcx>>>(
        tcx: TyCtxt<'tcx>,
        path: &Path,
        meta: T,
    ) -> Result<(), io::Error> {
        let _ = std::fs::File::create(path)?;
        std::fs::create_dir_all(path.parent().unwrap())?;

        let hygiene_context = HygieneEncodeContext::default();

        let mut encoder = DefSpecsEncoder {
            tcx,
            opaque: opaque::FileEncoder::new(path)?,
            type_shorthands: Default::default(),
            predicate_shorthands: Default::default(),
            interpret_allocs: Default::default(),
            hygiene_context: &hygiene_context,
            symbol_table: Default::default(),
        };

        meta.encode(&mut encoder);
        encoder.finish().map_err(|e| e.1)
    }

    pub fn finish(mut self) -> Result<(), (PathBuf, Error)> {
        self.opaque.finish()?;
        Ok(())
    }
}

// Taken from rustc:
// https://doc.rust-lang.org/nightly/nightly-rustc/rustc_metadata/rmeta/encoder/macro.encoder_methods.html
macro_rules! encoder_methods {
    ($($name:ident($ty:ty);)*) => {
        $(fn $name(&mut self, value: $ty) -> () {
            self.opaque.$name(value)
        })*
    }
}
impl<'a, 'tcx> Encoder for DefSpecsEncoder<'a, 'tcx> {
    encoder_methods! {
        emit_usize(usize);
        emit_u128(u128);
        emit_u64(u64);
        emit_u32(u32);
        emit_u16(u16);
        emit_u8(u8);

        emit_isize(isize);
        emit_i128(i128);
        emit_i64(i64);
        emit_i32(i32);
        emit_i16(i16);
        emit_i8(i8);

        emit_bool(bool);
        emit_char(char);
        emit_str(&str);
        emit_raw_bytes(&[u8]);
    }
}

impl<'a, 'tcx> SpanEncoder for DefSpecsEncoder<'a, 'tcx> {
    fn encode_span(&mut self, span: Span) {
        let sm = self.tcx.sess.source_map();
        let local_crate_stable_id = self.tcx.stable_crate_id(LOCAL_CRATE);
        for bp in [span.lo(), span.hi()] {
            let sf = sm.lookup_source_file(bp);

            let ssfi =
                StableSourceFileId::from_filename_for_export(&sf.name, local_crate_stable_id);
            ssfi.encode(self);
            // Not sure if this is the most stable way to encode a BytePos. If it fails
            // try finding a function in `SourceMap` or `SourceFile` instead. E.g. the
            // `bytepos_to_file_charpos` fn which returns `CharPos` (though there is
            // currently no fn mapping back to `BytePos` for decode)
            (bp - sf.start_pos).encode(self);
        }
    }
    fn encode_symbol(&mut self, sym: Symbol) {
        // if symbol preinterned, emit tag and symbol index
        if sym.is_preinterned() {
            self.opaque.emit_u8(SYMBOL_PREINTERNED);
            self.opaque.emit_u32(sym.as_u32());
        } else {
            // otherwise write it as string or as offset to it
            match self.symbol_table.entry(sym) {
                Entry::Vacant(o) => {
                    self.opaque.emit_u8(SYMBOL_STR);
                    let pos = self.opaque.position();
                    o.insert(pos);
                    self.emit_str(sym.as_str());
                }
                Entry::Occupied(o) => {
                    let x = *o.get();
                    self.emit_u8(SYMBOL_OFFSET);
                    self.emit_usize(x);
                }
            }
        }
    }

    fn encode_expn_id(&mut self, eid: ExpnId) {
        self.hygiene_context.schedule_expn_data_for_encoding(eid);
        eid.krate.encode(self);
        eid.local_id.as_u32().encode(self);
    }
    fn encode_syntax_context(&mut self, ctx: SyntaxContext) {
        raw_encode_syntax_context(ctx, self.hygiene_context, self);
    }
    fn encode_crate_num(&mut self, cnum: CrateNum) {
        self.tcx.stable_crate_id(cnum).encode(self)
    }
    fn encode_def_index(&mut self, _: DefIndex) {
        panic!("encoding `DefIndex` without context");
    }
    fn encode_def_id(&mut self, id: DefId) {
        self.tcx.def_path_hash(id).encode(self)
    }
}

impl<'a, 'tcx> TyEncoder for DefSpecsEncoder<'a, 'tcx> {
    type I = TyCtxt<'tcx>;
    const CLEAR_CROSS_CRATE: bool = true;

    fn position(&self) -> usize {
        self.opaque.position()
    }

    fn type_shorthands(&mut self) -> &mut FxHashMap<Ty<'tcx>, usize> {
        &mut self.type_shorthands
    }

    fn predicate_shorthands(&mut self) -> &mut FxHashMap<ty::PredicateKind<'tcx>, usize> {
        &mut self.predicate_shorthands
    }

    fn encode_alloc_id(&mut self, alloc_id: &rustc_middle::mir::interpret::AllocId) {
        let (index, _) = self.interpret_allocs.insert_full(*alloc_id);

        index.encode(self)
    }
}
