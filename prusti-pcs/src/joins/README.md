# Repackers
A repacker is an algorithm which takes one or many permission sets as input, and outputs a sequence of operations which manipulate that permission set into a state. 

## Permissions as a Lattice
Central to the repackers is the idea that permission sets form lattices in several ways; this fact is utilized to repack disparate permission sets to extremal (namely, unique) states. Let ``unpack`` be the partial function from places to the sets they unpack to, with permissions (so if ``unpack (e p) = {e p.f, e p.g, ...}`` then ``unpack (u p) = {u p.f, u p.g, ...}``). We will be ambiguous about packs/unpacks as a set (the afformentioned definition) and a partial function from permission sets to permission sets. 

Two permission sets ``P`` and ``Q`` have the same *footprint* if there exists a sequence of ``pack`` and ``unpack`` which can be applied in sequence to ``P`` to yield ``Q`` (we will denote this equivalence relation on permission sets by ``P ~ Q``)


- Define the *weakening order* as the reflexive, transitive closure of the following relation on equvalence classes of ``~`` by 
```
            ------------------- (weaken-e)
               {u p} <= {e p}


            ------------------- (weaken-u)
                { } <= {e p}


                 P <= Q               
           ----------------- provided P U R, Q U R well defined* (framing)
             P U R <= Q U R

     *U is the separating union, if valid. That is, {f} U {f.g} is not allowed.
```
(ignoring for clarity details of well-definedness and antisymmetry). This partial order has a unique bottom ``{ }``, and so every pair of permission sets has a lower bound. Every pair of permission sets also has a unique meet: we will prove this later after with a repacking algorithm to construct it. 


- Within equivalence classes of ``~``, we can define the *packing order* as the reflexive, transitive closure of 
```
            ------------------- provided unpack p well defined (packing)
               unpack p <= p


                 P <= Q               
            ----------------- provided P U R, Q U R well defined* (framing)
             P U R <= Q U R

     *U is the separating union, if valid. That is, {f} U {f.g} is not allowed.
```
This order does not have a bottom since references can be arbitrarily unpacked (see for example, a linked list). We will prove it has a unique top. 

TODO: continue this.

