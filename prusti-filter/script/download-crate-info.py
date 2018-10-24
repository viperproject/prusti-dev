#!/usr/bin/python3

"""Download information about crates on crates.io."""

import json
import os
import time
import urllib.request
import re
import shutil
import subprocess
import sys
import csv


ROOT = os.path.abspath('.')
CRATES_PATH = os.path.join(ROOT, 'crates')

# Path to a local copy of
# https://github.com/rust-lang/crates.io-index.git
CRATES_INDEX_PATH = os.path.join(CRATES_PATH, 'index')
assert os.path.exists(CRATES_INDEX_PATH)

# Path to a location with all information about each crate.
CRATES_INFO_PATH = os.path.join(CRATES_PATH, 'info')
if not os.path.exists(CRATES_INFO_PATH):
    os.mkdir(CRATES_INFO_PATH)

# Directory in which crates are built.
COMPILATION_PATH = os.path.join(CRATES_PATH, 'compilation')

# API of crates.io.
CRATES_URL = 'https://crates.io'
CRATES_API_URL = CRATES_URL + '/api/v1/crates'


def collect_crates():
    crates = []
    for root, dirs, files in os.walk(CRATES_INDEX_PATH):
        if '.git' in dirs:
            dirs.remove('.git')
        crates.extend([
            (root.replace(CRATES_INDEX_PATH, CRATES_INFO_PATH), file_name)
            for file_name in files
            if not file_name.endswith('.json')])
    return crates


class CrateInfo:

    def __init__(self, *args):
        self.info = args


def check_version(version):
    version = version.replace('-alpha', '')
    version = version.replace('-beta', '')
    assert len([int(part) for part in version.split('.')]) == 3

def download_crate_info(directory, crate_name):
    try:
        url = '{}/{}'.format(CRATES_API_URL, crate_name)
        with urllib.request.urlopen(url) as response:
            code = response.code
            data = response.read().decode('utf-8')
            data = json.loads(data)
        path = os.path.join(directory, 'data.json')
        with open(path, 'w') as fp:
            json.dump(data, fp, indent=4)
        max_version = data['crate']['max_version']
        identifier = data['crate']['id']
        name = data['crate']['name']
        downloads = data['crate']['downloads']
        recent_downloads = data['crate']['downloads']
        check_version(max_version)
        version_info = [
            version
            for version in data['versions']
            if version['num'] == max_version
        ][0]
        dependencies_url = CRATES_URL + version_info['links']['dependencies']
        with urllib.request.urlopen(dependencies_url) as response:
            code = response.code
            dependencies = response.read().decode('utf-8')
            dependencies = json.loads(dependencies)
        path = os.path.join(directory, 'dependencies.json')
        with open(path, 'w') as fp:
            json.dump(dependencies, fp, indent=4)
        dependency_count = len(dependencies['dependencies'])
        return CrateInfo(
            identifier,
            name,
            max_version,
            dependency_count,
            downloads,
            recent_downloads,
            version_info['dl_path'],
            )
    except Exception as e:
        print(e)
        return None


def compile_crate(directory, crate_name, crate_info):
    if os.path.exists(COMPILATION_PATH):
        shutil.rmtree(COMPILATION_PATH)
    os.mkdir(COMPILATION_PATH)
    toml_path = os.path.join(COMPILATION_PATH, 'Cargo.toml')
    with open(toml_path, 'w') as fp:
        toml.dump({
            'dependencies': {
                crate_name: crate_info.max_version,
                },
            'package': {
                'name': 'compilation_01',
                'version': '0.1.0',
                }
            }, fp)
    src_dir = os.path.join(COMPILATION_PATH, 'src')
    os.mkdir(src_dir)
    with open(os.path.join(src_dir, 'lib.rs'), 'w') as fp:
        fp.write('')
    stdout_file = os.path.join(directory, 'stdout')
    stderr_file = os.path.join(directory, 'stderr')
    with open(stdout_file, 'w') as fout:
        with open(stderr_file, 'w') as ferr:
            result = subprocess.run(
                args=['/data/toolchain/bin/cargo', 'build', '--verbose'],
                stdout=fout,
                stderr=ferr,
                # Give 5 minutes for each crate.
                timeout=(crate_info.dependency_count + 1)*5*60,
                cwd=COMPILATION_PATH,
                env={
                    "RUST_BACKTRACE": "1",
                    "PATH": "/usr/local/sbin:/usr/local/bin:"
                            "/usr/sbin:/usr/bin:/sbin:/bin",
                    "SCCACHE_DIR": "/data/cache",
                    "LD_LIBRARY_PATH": "/data/toolchain/lib/",
                    "RUSTC_WRAPPER": "/home/developer/.cargo/bin/sccache",
                    "RUSTC": "/data/toolchain/bin/rustc",
                },
            )
            if result.returncode != 0:
                print('FAILED', end=' ')
    print(directory, end=' ')


def check_crate(directory, crate_name):
    os.makedirs(directory, exist_ok=True)
    directory = os.path.join(directory, crate_name)
    if not os.path.exists(directory):
        os.mkdir(directory)
        crate_info = download_crate_info(directory, crate_name)
        return crate_info
        # if crate_info is not None:
            # compile_crate(directory, crate_name, crate_info)


def check_crates(crates):
    with open(os.path.join(CRATES_PATH, 'log.csv'), 'w') as fp:
        writer = csv.writer(fp)
        for i, (directory, crate_name) in enumerate(crates):
            crate_info = check_crate(directory, crate_name)
            if crate_info is not None:
                writer.writerow(crate_info.info)
            print("{:5d}/{} {}".format(i, len(crates), crate_name))


def crates_to_paths(crates):
    return [os.path.join(*crate) for crate in crates]


def check_all_exists(paths):
    error = False
    for path in paths:
        if not os.path.exists(path):
            print("Missing: " + path)
            error = True
    if error:
        raise Exception("STOP")


def main():
    crates = collect_crates()
    check_crates(crates)
    # paths = crates_to_paths(crates)
    # check_all_exists(paths)


if __name__ == '__main__':
    main()
