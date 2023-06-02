#!env/bin/python3

import datetime

import z3


class PermissionGrouping(z3.UserPropagateBase):

    def __init__(self, s=None, ctx=None):
        z3.UserPropagateBase.__init__(self, s, ctx)
        self.add_fixed(lambda x, v : self._fixed(x, v))
        self.add_final(lambda : self._final())
        self.add_eq(lambda x, y : self._eq(x, y))
        self.add_created(lambda t : self._created(t))
        print("created")

    def push(self):
        print("push!")

    def pop(self, n):
        print("pop!")

    def fresh(self, new_ctx):
        print("fresh!")

    def _fixed(self, x, v):
        print("_fixed!")

    def _final(self, x, v):
        print("_final!")

    def _eq(self, x, v):
        print(f"_eq!: {x} {v}")

    def _created(self, x, v):
        print("_created!")

class State:
    def __init__(self):
        self.address_sort = z3.DeclareSort('Address')
        self.perm_sort = z3.RealSort()
        self._full_permission = z3.RealVal("1")
        self._no_permission = z3.RealVal("0")
        self.solver = z3.Solver()
        self.permission_grouping = PermissionGrouping(self.solver)
        self.locations = []
        self.permissions = []
        self.sum = []
        self.non_negativity_assumptions = []
        self.exhaled_location = self.fresh_location()

    def fresh_location(self):
        location = z3.Const(f"address${len(self.locations)}", self.address_sort)
        self.locations.append(location)
        self.permission_grouping.add(location)
        return location

    def fresh_permission(self):
        permission = z3.Const(f"permission${len(self.permissions)}", self.perm_sort)
        self.permissions.append(permission)
        return permission

    def full_permission(self):
        return self._full_permission

    def add_summand(self, location, permission):
        self.sum.append(
            z3.If(self.exhaled_location == location, permission, self._no_permission)
        )

    def is_non_negative_assertion(self):
        sum_expr = self._no_permission
        for summand in self.sum:
            sum_expr = sum_expr + summand
        return sum_expr >= self._no_permission

    def generate_sum(self):
        sum_expr = self._no_permission
        for summand in self.sum:
            sum_expr = sum_expr + summand
        return sum_expr

    def is_full_assertion(self):
        sum_expr = self._no_permission
        for summand in self.sum:
            sum_expr = sum_expr + summand
        return sum_expr >= self._full_permission

    def add_non_negativity_assumption(self):
        self.solver.push()
        assertion = self.is_non_negative_assertion()
        self.solver.add(assertion)

    # def check_assertion(self, assertion):
    #     assertion = z3.Not(assertion)
    #     # print(assertion)
    #     self.solver.push()
    #     self.solver.add(assertion)
    #     print("checking: {assertion}")
    #     print(self.solver)
    #     start = datetime.datetime.now()
    #     result = self.solver.check()
    #     self.solver.pop()
    #     end = datetime.datetime.now()
    #     print(f"  start: {start}")
    #     print(f"  end: {end}")
    #     print(f"  duration: {end-start}")
    #     return result

    # def check_assertion2(self, assertion):
    #     assertion = z3.Not(assertion)
    #     solver = z3.Solver()
    #     solver.add(assertion)
    #     start = datetime.datetime.now()
    #     result = solver.check()
    #     end = datetime.datetime.now()
    #     print(f"  start: {start}")
    #     print(f"  end: {end}")
    #     print(f"  duration: {end-start}")
    #     return result

def construct_sum(exhaled_location, locations, permission, no_permission):
    sum_expr = no_permission
    for location in locations:
        sum_expr = sum_expr + z3.If(
            exhaled_location == location,
            permission,
            no_permission,
        )
    return sum_expr

def check_size(size, add_group_assumptions):
#   print(f"size: {size}")
    state = State()
    state.solver.push()
    locations = []
    for _ in range(size):
        locations.append(state.fresh_location())
    assertion = z3.BoolVal(True)
    for (i, exhaled_location) in enumerate(locations):
    #   print(i, exhaled_location)
        inhaled_sum = construct_sum(
            exhaled_location, locations, state._full_permission, state._no_permission)
    #   print(inhaled_sum)
        exhaled_sum = construct_sum(
            exhaled_location, locations[:i], -state._full_permission, state._no_permission)
    #   print(exhaled_sum)
        check = inhaled_sum + exhaled_sum >= state._full_permission
    #   print(check)
        assertion = z3.And(assertion, check)

        if add_group_assumptions:
            for (j, location_group) in enumerate(locations):
                inhaled = z3.If(
                    exhaled_location == location_group,
                    state._full_permission,
                    state._no_permission,
                )
                exhaled = z3.If(
                    exhaled_location == location_group,
                    -state._full_permission,
                    state._no_permission,
                )
                if j < i:
                    conjunct = inhaled + exhaled >= 0
                else:
                    conjunct = inhaled >= 0
        #       print(conjunct)
                assertion = z3.And(assertion, conjunct)

#   print(assertion)
    assertion = z3.Not(assertion)
    state.solver.add(assertion)
    start = datetime.datetime.now()
    result = state.solver.check()
    end = datetime.datetime.now()
    print(f"  start: {start}")
    print(f"  end: {end}")
    print(f"  duration: {end-start}")
    print(result)
#   print(f"Size {size} completed in {end-start}")
    # add_group_assumptions=False
    # Size 1 completed in 0:00:00.005373
    # Size 2 completed in 0:00:00.006233
    # Size 3 completed in 0:00:00.006431
    # Size 4 completed in 0:00:00.009251
    # Size 5 completed in 0:00:00.011879
    # Size 6 completed in 0:00:00.013903
    # Size 7 completed in 0:00:00.018198
    # Size 8 completed in 0:00:00.020426
    # Size 9 completed in 0:00:00.027054
    # Size 10 completed in 0:00:00.045473
    # Size 11 completed in 0:00:00.078226
    # Size 12 completed in 0:00:00.149595
    # Size 13 completed in 0:00:00.280547
    # Size 14 completed in 0:00:00.558921
    # Size 15 completed in 0:00:01.145783
    # Size 16 completed in 0:00:02.419031
    # Size 17 completed in 0:00:05.444189
    # Size 18 completed in 0:00:10.202696
    # Size 19 completed in 0:00:28.442166
    # Size 20 completed in 0:01:32.388904
    # add_group_assumptions=True
    # Size 1 completed in 0:00:00.006661
    # Size 2 completed in 0:00:00.008673
    # Size 3 completed in 0:00:00.008395
    # Size 4 completed in 0:00:00.012773
    # Size 5 completed in 0:00:00.012729
    # Size 6 completed in 0:00:00.014022
    # Size 7 completed in 0:00:00.012290
    # Size 8 completed in 0:00:00.016343
    # Size 9 completed in 0:00:00.021220
    # Size 10 completed in 0:00:00.024776
    # Size 11 completed in 0:00:00.032785
    # Size 12 completed in 0:00:00.041238
    # Size 13 completed in 0:00:00.046568
    # Size 14 completed in 0:00:00.069082
    # Size 15 completed in 0:00:00.457555
    # Size 16 completed in 0:00:00.212668
    # Size 17 completed in 0:00:00.139427
    # Size 18 completed in 0:00:00.176176
    # Size 19 completed in 0:00:00.180726

def main():
    # for i in range(1, 10):
    #     check_size(i, False)
    check_size(3, False)

if __name__ == '__main__':
    main()
