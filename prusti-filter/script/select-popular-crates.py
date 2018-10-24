#!/usr/bin/python3

import os
import csv
import sys

ROOT = os.path.abspath('.')
CRATES_PATH = os.path.join(ROOT, 'crates')
CRATE_INFO_PATH = os.path.join(CRATES_PATH, 'log.csv')
CRATE_DOWNLOAD_SCRIPT = os.path.join(CRATES_PATH, 'download.sh')
CRATE_ANALYSE_SCRIPT = os.path.join(CRATES_PATH, 'analyse.sh')
CARGO_BUILD_SCRIPT=os.path.join(ROOT, 'script', 'cargo-build.sh')

def select_crates(crate_download_folder, count):
    crate_download_folder = os.path.abspath(crate_download_folder)
    crates = []
    with open(CRATE_INFO_PATH, 'r') as fp:
        reader = csv.reader(fp)
        for row in reader:
            recent_downloads = int(row[-2])
            crates.append((recent_downloads, row))
    crates.sort()
    crates = list(zip(range(count), reversed(crates)))
    with open(CRATE_DOWNLOAD_SCRIPT, 'w') as fp:
        def write(s, *args, **kwargs):
            fp.write(s.format(*args, **kwargs))
        write("#!/bin/bash\n")
        write("\n")
        for i, (_, crate) in crates:
            identifier = crate[0]
            write("# {:3d} id={} name={}\n", i, identifier, crate[1])
            download_folder = os.path.join(
                crate_download_folder,
                '{:03d}_'.format(i) + identifier)
            download_target = os.path.join(download_folder, 'crate.tar.gz')
            write("mkdir -p '{}'\n", download_folder)
            write("wget -c 'https://crates.io{}' -O {}\n", crate[-1], download_target)
            extract_directory = os.path.join(download_folder, 'source')
            write("mkdir -p '{}'\n", extract_directory)
            write("tar -xf '{}' --directory='{}' --strip-components=1\n", download_target, extract_directory)
            write("\n")

    with open(CRATE_ANALYSE_SCRIPT, 'w') as fp:
        def write(s, *args, **kwargs):
            fp.write(s.format(*args, **kwargs))
        write("#!/bin/bash\n")
        write("\n")
        write("cargo build\n")
        for i, (_, crate) in crates:
            identifier = crate[0]
            write("# {:3d} id={} name={}\n", i, identifier, crate[1])
            download_folder = os.path.join(
                crate_download_folder,
                '{:03d}_'.format(i) + identifier)
            extract_directory = os.path.join(download_folder, 'source')
            write("cd '{}'\n", extract_directory)
            write("cargo clean\n")
            write("bash '{}'\n", CARGO_BUILD_SCRIPT)
            write("\n")

def main(crate_download_folder):
    select_crates(crate_download_folder, 500)


if __name__ == '__main__':
    main(sys.argv[1])
