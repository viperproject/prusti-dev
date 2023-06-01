#!/usr/bin/python3

import z3

class State:
    def __init__(self):
        self.address_sort = z3.DeclareSort('Address')
        self.solver = z3.Solver()
        self.locations = []

    def fresh_location(self):
        location = z3.Const(f"address${len(self.locations)}", self.address_sort)
        self.locations.append(location)
        return location

def main():
    state = State()

    location = state.fresh_location()

if __name__ == '__main__':
    main()
