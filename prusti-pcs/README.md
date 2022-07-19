# Computation of an interface between Prusti and Rustc 

Run with the feature flag ``dump_operational_pcs`` to compute. 

## TODO

 - [ ] Straight line, unshared code
    - [x] refactor
    - [x] 1-ary propagation method (repacker)
        - [x] temporaries
        - [x] uninit
        - [x] apply-packing
        - [x] separating union
        - [ ] refactor
        - [x] fix lifetimes
        - [ ] change pcs-after back to pcs-before again
    - [ ] formalize poset interpretation of places
    - [x] MIR -> MicroMIR translation
    - [ ] stable output representation for testing
        - [ ] serialization
    - [ ] graphviz output
    - [ ] test harness
        - [ ] tests
 - [ ] Branches
    - [ ]


- Maintainence
    - [ ] turn moves into borrows
