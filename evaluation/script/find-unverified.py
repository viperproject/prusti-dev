#!/usr/bin/python3

"""Find functions from the white-listed ones that were not verified."""

import csv
import os
import sys


def extract_whitelist(prusti_toml):
    with open(prusti_toml) as fp:
        whitelist = []
        append = False
        for line in fp:
            if line.startswith(']'):
                append = False
            if append:
                line = line.replace('",\n', '').replace('"', '').replace('\n', '')
                whitelist.append(line)
            if line.startswith('WHITELIST = ['):
                append = True
    return whitelist


def extract_verified_methods(report_csv):
    with open(report_csv) as fp:
        reader = csv.reader(fp)
        verified_methods = []
        for row in reader:
            if row[0] == 'EntitySuccessMessage':
                method = (row[1]
                    .replace('$opensqu$', '[')
                    .replace('$closesqu$', ']')
                    .replace('$opencur$', '{')
                    .replace('$closecur$', '}')
                    .replace('$$', '::')
                )
                if method.startswith('m_'):
                    verified_methods.append(method[2:])
    return verified_methods


def main(crate_path):
    report_csv = os.path.join(crate_path, 'report.csv')
    prusti_toml = os.path.join(crate_path, 'Prusti.toml')

    verified_methods = extract_verified_methods(report_csv)
    whitelist = extract_whitelist(prusti_toml)
    for whitelisted_method in whitelist:
        if whitelisted_method not in verified_methods:
            print(whitelisted_method)


if __name__ == '__main__':
    main(sys.argv[1])
