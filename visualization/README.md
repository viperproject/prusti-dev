The visualization renders the MIR CFG on the left-hand side; the right-hand side
shows the state of the PCS after a given statement. You can select the statement
in the MIR by clicking on it. Arrow keys can also be used to move up and down
between statements in a basic block.

To run the visualization:

1. Run Prusti on a file, e.g. `prusti-rustc borrow.rs`. This will generate a
   JSON dump of the MIR CFG and DOT files for PCS states for each function
   verified.
2. Run a webserver with `visualization` as the root directory. For example you
   can in this folder run the command: `python3 -m http.server`
3. Go to http://localhost:8000/ to view the visualization
