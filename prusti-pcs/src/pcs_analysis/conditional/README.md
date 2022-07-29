# Conditional PCS

The conditional PCS maintains several invariants:
 - The PCS's exclusive permissions are equal to Initialized permissions
 - The PCS's uninit permissions are equal to Allocated and not Initialized permissions

To attain these invariants, which are in general the result of fixed point analyses, we must implement a rule for combining PCS's. In the case of owned-only code, we have the following important monotonicity property
```
The PCS before any join is strictly stronger than the inferred PCS after the join
```
where "stronger" is interpreted in the permission lattice sense (1).

We impose an additional assumption:
```
lemma: We can always fully pack before applying a terminator, and the result is fully packed.
argument: By cases on the terminator.
    Jump: no conditions
    Jump int: no conditions
    Return: _0 is fully packed 
    FailVerif: bottom
```

also assumed by the analysis crate, that terminators postconditions are uniform... this is true for the MIR because we are not verifiying along error paths and the only other conditional is IF which 

```
Algorithm JOIN

Input: 
```



(1) *note*: This is a key property we should keep in mind for the borrows case. 