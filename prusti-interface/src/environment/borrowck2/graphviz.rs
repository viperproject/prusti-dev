use std::{
    collections::{HashMap, HashSet},
    fs::File,
    io::{self, BufWriter, Write},
    path::Path,
};
use super::MirBody;

struct GraphvizFile {
    output: std::cell::RefCell<BufWriter<File>>,
}

impl GraphvizFile {
    fn new(path: &Path) -> IoResult<Self> {
        let output_file = File::create(path)?;
        let output = std::cell::RefCell::new(BufWriter::new(output_file));
        Ok(Self {
            output
        })
    }
}

struct GraphvizWriter<'tcx, 'a> {
    output: GraphvizFile,
    body: &'a MirBody<'tcx>,
}

macro_rules! write_graph {
    ( $self:ident, $( $x:expr ),* ) => {
        writeln!($self.output.output.borrow_mut(), $( $x ),*)?;
    }
}

impl<'tcx, 'a> GraphvizWriter<'tcx, 'a> {
    fn new(path: &Path, body: &'a MirBody<'tcx>) -> IoResult<Self> {
        let output = GraphvizFile::new(path)?;
        Ok(Self {
            output, body
        })
    }
    fn write_all(&self) -> IoResult {
        write_graph!(self, "digraph G {{\n");
        write_graph!(self, "}}\n");
        Ok(())
    }
}

type IoResult<T=()> = Result<T, io::Error>;

impl<'tcx> MirBody<'tcx> {
    // pub fn to_graphviz<'a>(&'a self, path: &'a Path) -> IoResult
        // where 'a: 'tcx
    pub fn to_graphviz(&self, path: &Path) -> IoResult
    {
        let writer = GraphvizWriter::new(path, self)?;
        writer.write_all()?;
        Ok(())
    }
}