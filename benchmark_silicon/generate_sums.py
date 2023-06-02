#!/usr/bin/python3

import z3
import datetime

class State:
    def __init__(self):
        self.address_sort = z3.DeclareSort('Address')
        self.perm_sort = z3.RealSort()
        self._full_permission = z3.RealVal("1")
        self._no_permission = z3.RealVal("0")
        self.solver = z3.Solver()
        self.locations = []
        self.permissions = []
        self.sum = []
        self.non_negativity_assumptions = []
        self.exhaled_location = self.fresh_location()

    def fresh_location(self):
        location = z3.Const(f"address${len(self.locations)}", self.address_sort)
        self.locations.append(location)
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

    def check_assertion(self, assertion):
        assertion = z3.Not(assertion)
        # print(assertion)
        self.solver.push()
        self.solver.add(assertion)
        print("checking: {assertion}")
#       print(self.solver)
        start = datetime.datetime.now()
        result = self.solver.check()
        self.solver.pop()
        end = datetime.datetime.now()
        print(f"  start: {start}")
        print(f"  end: {end}")
        print(f"  duration: {end-start}")
        return result

    def check_assertion2(self, assertion):
        assertion = z3.Not(assertion)
        solver = z3.Solver()
        solver.add(assertion)
        start = datetime.datetime.now()
        result = solver.check()
        end = datetime.datetime.now()
        print(f"  start: {start}")
        print(f"  end: {end}")
        print(f"  duration: {end-start}")
        return result

def main():
    state = State()

    full_permission = state.full_permission()

    # TODO: If the original program does not have disjunctive aliasing, it
    # is always enought to do experiment with non-negativity.

#   TODO: check unsat of a sequence of implications:
#       s1 = 0
#       s1 >= 0
#       s2 = s1 + ...
#       s1 >= 0 ==> s2 >= 0
#       s3 = s2 + ...
#       s2 >= 0 and s1 >= 0 ==> s3 >= 0

    sum_expr = state._no_permission
    sum_expr_assume = z3.BoolVal(True)

    for i in range(3):
        print(f"size: {i}")
        location = state.fresh_location()

        sum_expr_add = sum_expr + z3.If(state.exhaled_location == location, state._full_permission, state._no_permission)
        sum_expr_assume_add = z3.And(sum_expr_assume, sum_expr_add >= 0)

        sum_expr_sub = sum_expr_add + z3.If(state.exhaled_location == location, -state._full_permission, state._no_permission)
        sum_expr_assume_sub = z3.And(sum_expr_assume_add, sum_expr_sub >= 0)

        sum_expr = sum_expr_sub
        sum_expr_assume = sum_expr_assume_sub

        print(sum_expr_assume)
        if i % 10 == 0:
            print(state.check_assertion2(sum_expr_assume))

if __name__ == '__main__':
    main()
