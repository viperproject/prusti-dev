#!/usr/bin/python3

import json
import os

ROOT = os.path.abspath('.')
ROSETTA_PATH = os.path.join(ROOT, 'rosetta')
RESULTS_PATH = os.path.join(ROSETTA_PATH, 'results.json')


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
    divisor = len(data['functions'])
    if divisor == 0:
        divisor = 100
    return (count/divisor,
            count,
            len(data['functions']),
            data['crate_name'])


def compute_reasons(results):
    counts = {}
    for example in results:
        for function in example['functions']:
            for restriction in function['procedure']['restrictions']:
                for key, value in restriction.items():
                    pair = (key, value)
                    try:
                        counts[pair] += 1
                    except KeyError as e:
                        counts[pair] = 1
    return counts


def show_reason(results, reason):
    """Print examples that have functions with given reason."""
    print("\nExamples with ", reason)
    crates = set()
    for example in results:
        for function in example['functions']:
            for restriction in function['procedure']['restrictions']:
                for key, value in restriction.items():
                    if value == reason:
                        crates.add(function['crate_name'])
    for crate in crates:
        print(crate)


def ignore_reason(results, reason):
    """Remove reason from results."""
    for example in results:
        for function in example['functions']:
            restrictions = function['procedure']['restrictions']
            remove = set()
            for i, restriction in enumerate(restrictions):
                for key, value in restriction.items():
                    if value == reason:
                        remove.add(i)
            function['procedure']['restrictions'] = [
                restriction
                for i, restriction in enumerate(restrictions)
                if i not in remove
                ]


def show_support_status(results, number=10):
    supported_count = 0
    total_count = 0
    supported_crates = []
    for example in results:
        supported_count += count_supported_functions(example)
        total_count += len(example['functions'])
        supported_crates.append(supported_functions_in_crate(example))
    print("Support {} of {} functions".format(supported_count, total_count))
    supported_crates.sort()
    supported_crates.reverse()
    print("Supported crates:")
    for i, (level, count, total, name) in zip(range(number), supported_crates):
        print('{:3d} {:.2f} {:2d} {:2d} {}'.format(i, level, count, total, name))


def show_problematic_reasons(results):
    reasons = compute_reasons(results)
    reason_counts = [(count, reason) for reason, count in reasons.items()]
    reason_counts.sort()
    reason_counts.reverse()
    for count, reason in reason_counts:
        print(count, reason)


def main():
    with open(RESULTS_PATH) as fp:
        results = json.load(fp)
    print("Number of examples:", len(results))

    show_support_status(results)
    # show_problematic_reasons(results)

    show_reason(results, 'mutable return type')
    show_reason(results, 'immutable return type')

    ignore_reason(results, 'mutable return type')
    ignore_reason(results, 'immutable return type')

    ignore_reason(results, 'lifetime parameters are partially supported')
    ignore_reason(results, 'mutable arguments are partially supported')
    ignore_reason(results, 'generic type parameters are not supported')
    ignore_reason(results, '`slice` types are not supported')
    ignore_reason(results, 'shared references are partially supported')

    show_support_status(results, 50)

# TODO: filter out modulo division, division, bit-operators.
# TODO: Filter out methods that contain less than 3 basic blocks. (Make
# prusti-filter to report function size in basic blocks.)


if __name__ == '__main__':
    main()
