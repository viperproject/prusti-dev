#!env/bin/python3

import datetime

import z3

address_sort = z3.DeclareSort('Address')
permission_mask_sort = z3.DeclareSort('PermissionMask')
perm_sort = z3.RealSort()
prop_sort = z3.BoolSort()
perm_empty = z3.PropagateFunction(
    "perm_empty", permission_mask_sort, prop_sort)
perm_update = z3.PropagateFunction(
    "perm_update", permission_mask_sort, address_sort, perm_sort, permission_mask_sort, prop_sort)
# perm_lookup = z3.PropagateFunction(
#     "perm_lookup", permission_mask_sort, address_sort, perm_sort)
perm_read = z3.PropagateFunction(
    "perm_read", permission_mask_sort, address_sort, perm_sort, prop_sort)
no_permission = z3.RealVal("0")

def location(index):
    return z3.Const(f"address${index}", address_sort)
def perm_mask(index):
    return z3.Const(f"perm_mask${index}", permission_mask_sort)
def perm_amount(index):
    return z3.Const(f"perm_amount${index}", perm_sort)

class PermissionGrouping(z3.UserPropagateBase):

    def __init__(self, s=None, ctx=None):
        z3.UserPropagateBase.__init__(self, s, ctx)
        self.add_fixed(lambda x, v : self._fixed(x, v))
        self.add_final(lambda : self._final())
        self.add_eq(lambda x, y : self._eq(x, y))
        self.add_created(lambda t : self._created(t))
        self._empty_masks = set()
        self._mask_derived_from = {}
        print("created")

    def push(self):
        print("push!")

    def pop(self, n):
        print("pop!")

    def fresh(self, new_ctx):
        print("fresh!")

    def _fixed(self, x, v):
        print("fixed: ", x, " := ", v)
        assert z3.is_true(v)
        if x.decl().eq(perm_empty):
            mask = x.arg(0)
            assert mask in self._empty_masks
        elif x.decl().eq(perm_update):
            mask = x.arg(0)
            address = x.arg(1)
            permission = x.arg(2)
            new_mask = x.arg(3)
            self._mask_derived_from[new_mask] = (mask, address, permission)
        # elif x.decl().eq(perm_lookup):
        #     mask = x.arg(0)
        #     address = x.arg(1)
        #     self.add(mask)
        #     self.add(address)
        #     self.add(x)
        elif x.decl().eq(perm_read):
            mask = x.arg(0)
            address = x.arg(1)
            value = x.arg(2)
            def compute_sum(mask):
                if mask in self._empty_masks:
                    return 0
                else:
                    (update_mask, update_address, update_permission) = self._mask_derived_from[mask]
                    return z3.If(address == update_address, update_permission, no_permission) + compute_sum(update_mask)
            assumption = value == compute_sum(mask)
            print("learned assumption:", assumption)
            self.propagate(assumption, [x])
        else:
            TODO

    def _final(self):
        print("Final")

    def _eq(self, x, v):
        print(f"_eq!: {x} {v}")

    def _created(self, t):
        print("Created", t)
        if t.decl().eq(perm_empty):
            mask = t.arg(0)
            self.add(mask)
            self._empty_masks.add(mask)
        elif t.decl().eq(perm_update):
            mask = t.arg(0)
            address = t.arg(1)
            permission = t.arg(2)
            new_mask = t.arg(3)
            self.add(mask)
            self.add(address)
            self.add(permission)
            self.add(new_mask)
        # elif t.decl().eq(perm_lookup):
        #     mask = t.arg(0)
        #     address = t.arg(1)
        #     self.add(mask)
        #     self.add(address)
        #     self.add(t)
        elif t.decl().eq(perm_read):
            mask = t.arg(0)
            address = t.arg(1)
            value = t.arg(2)
            self.add(mask)
            self.add(address)
            self.add(value)
        else:
            TODO

def check_size(size):
    solver = z3.Solver()
    pg = PermissionGrouping(solver)

    p0 = perm_mask(0)
    p1 = perm_mask(1)
    p2 = perm_mask(2)
    p3 = perm_mask(3)
    p4 = perm_mask(4)

    a0 = location(0)
    a1 = location(1)

    v0 = perm_amount(0)

    solver.add(perm_empty(p0))
    # inhale acc(a0)
    solver.add(perm_update(p0, a0, 1.0, p1))
    # inhale acc(a1)
    solver.add(perm_update(p1, a1, 1.0, p2))
    # exhale acc(a0)
    solver.add(perm_read(p2, a0, v0))
    solver.add(z3.Not(v0 >= 1.0))

    print(solver)
    print(solver.check())

def main():
    check_size(3)

if __name__ == '__main__':
    main()
