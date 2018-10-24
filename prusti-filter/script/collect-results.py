#!/usr/bin/python3

import glob
import os
import sys


ROOT = os.path.abspath('.')
CRATES_PATH = os.path.join(ROOT, 'crates')
RESULTS_PATH = os.path.join(CRATES_PATH, 'results.json')

def collect(crate_download_folder):
    print(glob.glob(os.path.join(crate_download_folder, '*', 'results.json')))


def main(crate_download_folder):
    collect(crate_download_folder)


if __name__ == '__main__':
    main(sys.argv[1])
