#/usr/bin/python3

import csv
import datetime
import glob
import os
import subprocess
import time
import re
import statistics

ROOT = os.path.dirname(os.path.abspath(__file__))
LOG_FILE = os.path.join(ROOT, 'bench.csv')


def main():
    examples = {}
    with open(LOG_FILE) as fp:
        reader = csv.reader(fp)
        for row in reader:
            (timestamp, path, _, _, total, verification, _, _, overflow) = row
            name = os.path.basename(path)
            print(timestamp, name, total, verification, overflow)
            key = (name, overflow)
            if key not in examples:
                examples[key] = []
            examples[key].append((total, verification))
    for ((name, overflow), values) in examples.items():
        print(name, overflow)
        totals = [float(total) for (total, _) in values]
        verifications = [float(verification) for (_, verification) in values]
        for (total, verification) in values:
            print("  ", total, verification)
        print("  total={:.0f}  ({:.0f})  verification={:.0f}  ({:.0f})".format(
            statistics.mean(totals), statistics.pstdev(totals),
            statistics.mean(verifications), statistics.pstdev(verifications)
        ))


if __name__ == '__main__':
    main()
