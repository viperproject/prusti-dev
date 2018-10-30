#!/usr/bin/python3

import json
import glob
import os
import sys


ROOT = os.path.abspath('.')
CRATES_PATH = os.path.join(ROOT, 'crates')
RESULTS_PATH = os.path.join(CRATES_PATH, 'prusti-filter-results.json')


def collect(crate_download_folder):
    crate_download_folder = os.path.abspath(crate_download_folder)
    all_data = []
    for root, dirs, files in os.walk(crate_download_folder):
        if 'prusti-filter-results.json' in files:
            path = os.path.join(root, 'prusti-filter-results.json')
            with open(path) as fp:
                data = json.load(fp)
                data['path'] = path
                all_data.append(data)
    with open(RESULTS_PATH, 'w') as fp:
        json.dump(all_data, fp, indent=2)

def count_supported_functions(data):
    count = 0
    for function in data['functions']:
        if not function['procedure']['restrictions']:
            count += 1
    return count


def supported_functions_in_crate(data):
    count = 0
    for function in data['functions']:
        if not function['procedure']['restrictions']:
            count += 1
    return (count/(len(data['functions'])+1.0),
            count,
            len(data['functions']),
            data['crate_name'])


def analyse(crate_download_folder):
    supported_functions = 0
    supported_crates = []
    for path in glob.glob(os.path.join(crate_download_folder, '*', 'prusti-filter-results.json')):
        with open(path) as fp:
            data = json.load(fp)
            supported_functions += count_supported_functions(data)
            supported_crates.append(supported_functions_in_crate(data))
    print("Supported functions: {}", supported_functions)
    supported_crates.sort()
    supported_crates.reverse()
    for i, (level, count, total, name) in zip(range(10), supported_crates):
        print(i, level, count, total, name)
    small_supported_crates = [crate for crate in supported_crates if crate[-2] < 50]
    for i, (level, count, total, name) in zip(range(10), small_supported_crates):
        print(i, level, count, total, name)


def main(crate_download_folder):
    collect(crate_download_folder)
    # analyse(crate_download_folder)


if __name__ == '__main__':
    main(sys.argv[1])
