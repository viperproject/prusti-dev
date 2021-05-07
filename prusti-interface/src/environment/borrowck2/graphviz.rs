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

macro_rules! to_html {
    ( $o:expr ) => {{
        format!("{:?}", $o)
            .replace("{", "\\{")
            .replace("}", "\\}")
            .replace("&", "&amp;")
            .replace(">", "&gt;")
            .replace("<", "&lt;")
            .replace("\n", "<br/>")
    }};
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
        self.print_temp_variables()?;
        write_graph!(self, "}}\n");
        Ok(())
    }
    fn print_temp_variables(&self) -> Result<(), io::Error> {
        write_graph!(self, "Variables [ style=filled shape = \"record\"");
        write_graph!(self, "label =<<table>");
        write_graph!(self, "<tr><td>VARIABLES</td></tr>");
        write_graph!(
            self,
            "<tr><td>Name</td><td>Temporary</td><td>Type</td><td>Region</td></tr>"
        );
        for local in self.body.iter_locals() {
            write_graph!(
                self,
                "<tr><td>{}</td><td>{:?}</td><td>{}</td><td>{}</td></tr>",
                local.name().unwrap_or(""),
                local.id(),
                to_html!(local.ty()),
                "todo: region"
            );
        }
        write_graph!(self, "</table>>];");
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