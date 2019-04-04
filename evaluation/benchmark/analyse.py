#/usr/bin/python3

import csv
import datetime
import glob
import os
import subprocess
import time
import re
import statistics

from benchmark import MANUAL_EVALUATION

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
    example_stats = {}
    for ((name, overflow), values) in examples.items():
        print(name, overflow)
        totals = [float(total) for (total, _) in values]
        verifications = [float(verification) for (_, verification) in values]
        for (total, verification) in values:
            print("  ", total, verification)
        stats = ("  total={:.1f}  ({:.1f})  verification={:.1f}  ({:.1f})".format(
            statistics.mean(totals), statistics.pstdev(totals),
            statistics.mean(verifications), statistics.pstdev(verifications)
        ))
        print(stats)
        assert name not in example_stats
        f = lambda x: "{:.1f}".format(x)
        example_stats[name] = (
            name,
            f(statistics.mean(totals)),
            f(statistics.pstdev(totals)),
            f(statistics.mean(verifications)),
            f(statistics.pstdev(verifications))
        )
    for example in MANUAL_EVALUATION:
        name = os.path.basename(example)
        print('{:40} {:5} {:5} {:5} {:5}'.format(*example_stats[name]))


if __name__ == '__main__':
    main()
