#!env/bin/python3

# Based on https://microsoft.github.io/z3guide/programming/Example%20Programs/User%20Propagator/

import datetime
import union_find
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
full_permission = z3.RealVal("1")

def location(index):
    return z3.Const(f"address${index}", address_sort)
permission_mask_counter = 0
def perm_mask():
    global permission_mask_counter
    permission_mask_counter += 1
    return z3.Const(f"perm_mask${permission_mask_counter}", permission_mask_sort)
perm_counter = 0
def perm_amount():
    global perm_counter
    perm_counter += 1
    return z3.Const(f"perm_amount${perm_counter}", perm_sort)

class PermissionGrouping(z3.UserPropagateBase):

    def __init__(self, s=None, ctx=None, group_terms=False):
        z3.UserPropagateBase.__init__(self, s, ctx)
        self.add_fixed(lambda x, v : self._fixed(x, v))
        self.add_final(lambda : self._final())
        self.add_eq(lambda x, y : self._eq(x, y))
        self.add_created(lambda t : self._created(t))
        self._empty_masks = set()
        self._mask_derived_from = {}
        self._group_terms = group_terms
        self.push_count = 0
        self.pop_count = 0
        self.lim = []
        self.trail = []
        self.uf = union_find.UnionFind(self.trail)

    def push(self):
        self.push_count += 1
        self.lim += [len(self.trail)]

    def pop(self, n):
        self.pop_count += n
        head = self.lim[len(self.lim) - n]
        while len(self.trail) > head:
            self.trail[-1]()
            self.trail.pop(-1)
        self.lim = self.lim[0:len(self.lim)-n]

    def fresh(self, new_ctx):
        TODO

    def _fixed(self, x, v):
        # print("fixed: ", x, " := ", v)
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
            groups = {}
            def compute_sum(mask):
                if mask in self._empty_masks:
                    return 0
                else:
                    (update_mask, update_address, update_permission) = self._mask_derived_from[mask]
                    summand = z3.If(address == update_address, update_permission, no_permission)
                    if self._group_terms:
                        node = self.uf.node(update_address)
                        root_term = self.uf.find(node).term
                        if root_term not in groups:
                            groups[root_term] = []
                        groups[root_term] += [(summand, update_permission)]
                    return summand + compute_sum(update_mask)
            assumption = value == compute_sum(mask)
            if self._group_terms:
                # print("groups:", groups)
                for group in groups.values():
                    sum_expression = z3.Sum([summand for (summand, _) in group])
                    sum_value = z3.simplify(sum([value for (_, value) in group]))
                    if sum_value.eq(no_permission) or sum_value.eq(full_permission):
                        assumption = z3.And(assumption, sum_expression >= 0)
            # print("learned assumption:", assumption)
            self.propagate(assumption, [x])
        else:
            TODO

    def _final(self):
        TODO

    def _eq(self, x, y):
        # print(f"_eq!: {x} {v}")
        self.uf.merge(x, y)

    def _created(self, t):
        if t.decl().eq(perm_empty):
            mask = t.arg(0)
            self.add(mask)
            self._empty_masks.add(mask)
        elif t.decl().eq(perm_update):
            mask = t.arg(0)
            address = t.arg(1)
            permission = t.arg(2)
            new_mask = t.arg(3)
            self.uf.node(address)
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
            self.uf.node(address)
            value = t.arg(2)
            self.add(mask)
            self.add(address)
            self.add(value)
        else:
            TODO

def check_size(size, group_terms):
    solver = z3.Solver()
    pg = PermissionGrouping(solver, group_terms=group_terms)

    mask = perm_mask()
    solver.add(perm_empty(mask))

    addresses = []
    for i in range(size):
        address = location(i)
        addresses.append(address)
        # inhale acc(address)
        new_mask = perm_mask()
        solver.add(perm_update(mask, address, 1.0, new_mask))
        mask = new_mask

    checks = z3.BoolVal(True)
    for (i, address) in enumerate(addresses):
        # exhale acc(address)
        value = perm_amount()
        solver.add(perm_read(mask, address, value))
        checks = z3.And(checks, value >= 1)
        new_mask = perm_mask()
        solver.add(perm_update(mask, address, -1.0, new_mask))
        mask = new_mask

    solver.add(z3.Not(checks))

    start = datetime.datetime.now()
    result = solver.check()
    end = datetime.datetime.now()

    # print(solver)
    # print(solver.check())
    print(f"Size {size} completed in {end-start} (push: {pg.push_count} pop: {pg.pop_count}) with {result}")

def main():
    # check_size(3, False)
    for i in range(3, 20):
        check_size(i, True)
    # group_terms=False
    # Size 3 completed in 0:00:00.006197 (push: 11 pop: 11) with unsat
    # Size 4 completed in 0:00:00.016547 (push: 50 pop: 50) with unsat
    # Size 5 completed in 0:00:00.026013 (push: 136 pop: 136) with unsat
    # Size 6 completed in 0:00:00.049699 (push: 264 pop: 264) with unsat
    # Size 7 completed in 0:00:00.082637 (push: 403 pop: 403) with unsat
    # Size 8 completed in 0:00:00.138415 (push: 599 pop: 599) with unsat
    # Size 9 completed in 0:00:00.225748 (push: 914 pop: 914) with unsat
    # Size 10 completed in 0:00:00.387808 (push: 1476 pop: 1476) with unsat
    # Size 11 completed in 0:00:00.695106 (push: 2542 pop: 2542) with unsat
    # Size 12 completed in 0:00:01.142290 (push: 3737 pop: 3737) with unsat
    # Size 13 completed in 0:00:02.020809 (push: 6086 pop: 6086) with unsat
    # Size 14 completed in 0:00:03.464235 (push: 10355 pop: 10355) with unsat
    # Size 15 completed in 0:00:06.745241 (push: 17012 pop: 17012) with unsat
    # Size 16 completed in 0:00:12.223822 (push: 31490 pop: 31490) with unsat
    # Size 17 completed in 0:00:28.458352 (push: 71376 pop: 71376) with unsat
    # Size 18 completed in 0:01:07.913775 (push: 163310 pop: 163310) with unsat
    # Size 19 completed in 0:02:37.331497 (push: 370474 pop: 370474) with unsat
    # group_terms=True
    # Size 3 completed in 0:00:00.008096 (push: 8 pop: 8) with unsat
    # Size 4 completed in 0:00:00.014301 (push: 26 pop: 26) with unsat
    # Size 5 completed in 0:00:00.023871 (push: 59 pop: 59) with unsat
    # Size 6 completed in 0:00:00.036188 (push: 126 pop: 126) with unsat
    # Size 7 completed in 0:00:00.062952 (push: 312 pop: 312) with unsat
    # Size 8 completed in 0:00:00.073902 (push: 335 pop: 335) with unsat
    # Size 9 completed in 0:00:00.110649 (push: 625 pop: 625) with unsat
    # Size 10 completed in 0:00:00.137818 (push: 733 pop: 733) with unsat
    # Size 11 completed in 0:00:00.163656 (push: 687 pop: 687) with unsat
    # Size 12 completed in 0:00:00.170364 (push: 1058 pop: 1058) with unsat
    # Size 13 completed in 0:00:00.226454 (push: 1301 pop: 1301) with unsat
    # Size 14 completed in 0:00:00.251802 (push: 1556 pop: 1556) with unsat
    # Size 15 completed in 0:00:00.342975 (push: 1925 pop: 1925) with unsat
    # Size 16 completed in 0:00:00.341066 (push: 2791 pop: 2791) with unsat
    # Size 17 completed in 0:00:00.394620 (push: 2708 pop: 2708) with unsat
    # Size 18 completed in 0:00:00.448467 (push: 3258 pop: 3258) with unsat
    # Size 19 completed in 0:00:00.471308 (push: 2988 pop: 2988) with unsat


if __name__ == '__main__':
    main()
