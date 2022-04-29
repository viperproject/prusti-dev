use rustc_middle::ty;

pub fn opaque_lifetime_string(index: usize) -> String {
    format!("bw{}", index)
}

pub trait LifetimeString {
    fn lifetime_string(&self) -> String;
}

impl LifetimeString for ty::RegionVid {
    fn lifetime_string(&self) -> String {
        opaque_lifetime_string(self.index())
    }
}

impl<'tcx> LifetimeString for ty::Region<'tcx> {
    fn lifetime_string(&self) -> String {
        match self.kind() {
            ty::ReEarlyBound(_) => {
                unimplemented!("ReEarlyBound: {}", format!("{}", self));
            },
            ty::ReLateBound(debruijn, bound_reg) => {
                format!("lft_late_{}_{}", debruijn.index(), bound_reg.var.index())
            },
            ty::ReFree(_) => {
                unimplemented!("ReFree: {}", format!("{}", self));
            },
            ty::ReStatic=> String::from("lft_static"),
            ty::ReVar(region_vid) => format!("lft_{}", region_vid.index()),
            ty::RePlaceholder(_) => {
                unimplemented!("RePlaceholder: {}", format!("{}", self));
            },
            ty::ReEmpty(_) => {
                unimplemented!("ReEmpty: {}", format!("{}", self));
            },
            ty::ReErased => String::from("lft_erased"),
        }
    }
}
