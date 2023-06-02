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

def construct_sum(exhaled_location, locations, permission, no_permission):
    sum_expr = no_permission
    for location in locations:
        sum_expr = sum_expr + z3.If(
            exhaled_location == location,
            permission,
            no_permission,
        )
    return sum_expr

def check_size(size):
    print(f"size: {size}")
    state = State()
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
        assertion = z3.And(assertion, inhaled_sum + exhaled_sum >= state._full_permission)

    #print(assertion)
    assertion = z3.Not(assertion)
    state.solver.add(assertion)
    start = datetime.datetime.now()
    result = state.solver.check()
    end = datetime.datetime.now()
    print(f"  start: {start}")
    print(f"  end: {end}")
    print(f"  duration: {end-start}")


def main():
    state = State()

    for i in range(1, 50):
        check_size(i)

if __name__ == '__main__':
    main()
