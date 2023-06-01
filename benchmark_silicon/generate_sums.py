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

    def check_assertion(self, assertion):
        assertion = z3.Not(assertion)
        # print(assertion)
        self.solver.push()
        self.solver.add(assertion)
        print("checking")
        start = datetime.datetime.now()
        result = self.solver.check()
        self.solver.pop()
        end = datetime.datetime.now()
        print(f"  start: {start}")
        print(f"  end: {end}")
        print(f"  duration: {end-start}")
        return result

def main():
    state = State()

    full_permission = state.full_permission()

    for i in range(100):
        print(f"size: {i}")
        location = state.fresh_location()

        state.add_summand(location, full_permission)
        state.add_summand(location, -full_permission)

        assertion = state.is_non_negative_assertion()
        print(state.check_assertion(assertion))

if __name__ == '__main__':
    main()
