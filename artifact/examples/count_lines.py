#!/usr/bin/python

import os
import glob


def count_lines(path):
    lines = [
        line
        for line in open(path).read().splitlines()
        if line.strip() and not line.strip().startswith('//')
    ]
    # print('\n'.join(lines))
    print(path, len(lines))


def main():
    root = os.path.abspath(os.path.dirname(__file__))
    for path in glob.glob(os.path.join(root, '*.rs.orig')):
        count_lines(path)

if __name__ == '__main__':
    main()
