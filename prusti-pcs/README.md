# Computation of an interface between Prusti and Rustc 

Run with the feature flag ``dump_operational_pcs`` to compute. 

## TODO

 - [ ] Straight line, unshared code
    - [x] refactor
    - [x] 1-ary propagation method (repacker)
        - [x] temporaries
        - [ ] uninit
        - [x] apply-packing
        - [ ] separating union
        - [ ] refactor
        - [x] fix lifetimes
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
