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
        - [x] refactor
        - [x] fix lifetimes
        - [x] change pcs-after back to pcs-before again
    - [ ] stable output representation for testing
        - [ ] serialization
    - [ ] formalize poset interpretation of places
    - [x] MIR -> MicroMIR translation
    - [ ] graphviz output
    - [ ] test harness
        - [ ] tests
 - [ ] Branches
    - [ ] implement conditional elaboration
        - [ ] repacker
            - [ ] operational description of conditional joins
            - [ ] terminator semantics should have only one postcondition
            - [ ] common PCS transformation interface (repack interface)
 - [ ] Borrows 
    - [ ] add type dependency to hoare semantics
    - [ ] ? 


- Maintainence
    - [ ] refactor out common data structures
    - [x] hoare semantics trait has Option baked in (why?), remove this 
    - [x] add explicit precondition to kill syntax
