# Packer
Constructs a sequence of packs and unpacks to unify two PCS's together, if it exists.


- PCS's naturally form a partial order, related to the subset partial order
```
                                                   P superset of Q
         -------------------- (packing)          ------------------- (sups)
            unpack p <= {p}                             P <= Q


                 P <= Q               
           ----------------- provided P U R, Q U R well defined* (framing)
             P U R <= Q U R

     *U is the separating union, if valid. That is, {f} U {f.g} is not allowed.
```
and they obey the regular partial order laws
```
                               P <= Q   Q <= R                 P <= Q   Q <= P
         ---------- (refl)   ------------------- (trans)     ------------------- (antisym)
           P <= P                  P <= R                            P = Q
```
where ``{}`` is the unique top. 


- pack/unpack do not change base local or exlusivity
    - Greatest meet can be computed individually for (base local)

- if a sequence of packs/unpacks unify two PCS's, it can be written as a sequence of unpacks followed by a sequence of packs
    - The unification computes the greatest meet, and then conclude by lattice well-definedness in this case. 
