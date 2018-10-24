#!/usr/bin/python3

import json
import glob
import os
import sys


ROOT = os.path.abspath('.')
CRATES_PATH = os.path.join(ROOT, 'crates')
RESULTS_PATH = os.path.join(CRATES_PATH, 'results.json')

def collect(crate_download_folder):
    all_data = []
    for path in glob.glob(os.path.join(crate_download_folder, '*', 'results.json')):
        with open(path) as fp:
            data = json.load(fp)
            all_data.append(data)
    with open(RESULTS_PATH, 'w') as fp:
        json.dump(all_data, fp)


def main(crate_download_folder):
    collect(crate_download_folder)


if __name__ == '__main__':
    main(sys.argv[1])
