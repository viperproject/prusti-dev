use prusti_rustc_interface::{
    span::{
        Span,
        BytePos,
    },
    middle::{
        ty::TyCtxt,
        hir::nested_filter::OnlyBodies,
    },
    hir::{intravisit::Visitor, BodyId},
};

// use rustc_middle::{hir::nested_filter::OnlyBodies, ty::TyCtxt};

// Most of this code is copied from flowistry! 
//



struct BodyFinder<'tcx> {
  tcx: TyCtxt<'tcx>,
  bodies: Vec<(Span, BodyId)>,
}

impl<'tcx> Visitor<'tcx> for BodyFinder<'tcx> {
  type NestedFilter = OnlyBodies;

  fn nested_visit_map(&mut self) -> Self::Map {
    self.tcx.hir()
  }

  fn visit_nested_body(&mut self, id: BodyId) {
    let hir = self.nested_visit_map();

    // const/static items are considered to have bodies, so we want to exclude
    // them from our search for functions
    if !hir
      .body_owner_kind(hir.body_owner_def_id(id))
      .is_fn_or_closure()
    {
      return;
    }

    let body = hir.body(id);
    self.visit_body(body);

    let hir = self.tcx.hir();
    let span = hir.span_with_body(hir.body_owner(id));

    if !span.from_expansion() {
      self.bodies.push((span, id));
    }
  }
}

pub fn find_bodies(tcx: TyCtxt) -> Vec<(Span, BodyId)> {
  let mut finder = BodyFinder {
    tcx,
    bodies: Vec::new(),
  };
  tcx.hir().visit_all_item_likes_in_crate(&mut finder);
  finder.bodies
}

pub fn find_enclosing_bodies(tcx: TyCtxt, sp: Span) -> impl Iterator<Item = BodyId> {
  let mut bodies = find_bodies(tcx);
  bodies.retain(|(other, _)| other.contains(sp));
  bodies.sort_by_key(|(span, _)| span_length(span));
  bodies.into_iter().map(|(_, id)| id)
}

pub fn charoffset_to_span(byte_start: u32, byte_end: u32, tcx: TyCtxt) -> Span {
    let source_map = tcx.sess.source_map();
    let offset = 0; // TODO: sometimes there might be a problem with 
                    // this approach! See to_span in range.rs, flowistry.

    // Span::with_root_ctxt(
    //   offset + BytePos(byte_start),
    //   offset + BytePos(byte_end),
    // )

    Span::with_root_ctxt(
      BytePos(byte_start),
      BytePos(byte_end),
    )
}

pub fn span_length(span: &Span) -> u32 {
    span.hi().0 - span.lo().0
}
