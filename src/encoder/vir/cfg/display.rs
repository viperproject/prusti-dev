// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use encoder::vir::cfg::method::*;
use std::fmt;

impl fmt::Display for CfgMethod {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        writeln!(
            f,
            "method {}({})",
            self.method_name,
            self.formal_args.iter().map(|x| format!("{:?}", x)).collect::<Vec<String>>().join(", ")
        )?;
        writeln!(
            f,
            "    returns ({})",
            self.formal_returns.iter().map(|x| format!("{:?}", x)).collect::<Vec<String>>().join(", ")
        )?;
        writeln!(f, "{{")?;
        for local_var in self.local_vars.iter() {
            writeln!(f, "    {:?}", local_var)?;
        }

        for (index, block) in self.basic_blocks.iter().enumerate() {
            writeln!(f, "  label {} // {}", self.basic_blocks_labels[index], index)?;
            for inv in &block.invs {
                writeln!(f, "    inv {}", inv)?;
            }
            for stmt in &block.stmts {
                writeln!(f, "    {}", stmt)?;
            }
            writeln!(f, "    {:?}", block.successor)?;
        }
        writeln!(f, "  label {}", RETURN_LABEL)?;
        writeln!(f, "}}")
    }
}
