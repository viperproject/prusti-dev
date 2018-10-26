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
            data['crate_name'],
            count,
            len(data['functions']),
            data['path'])


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
    crates = []
    for example in results:
        for function in example['functions']:
            for restriction in function['procedure']['restrictions']:
                for key, value in restriction.items():
                    if value == reason:
                        crates.append((function['crate_name'], function['node_path']))
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


def drop_small_functions(results, min_size):
    """Remove functions that are smaller than ``min_size`` from ``results``."""
    for example in results:
        functions = []
        for function in example['functions']:
            if function['procedure']['basic_block_count'] >= min_size:
                functions.append(function)
        example['functions'] = functions


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
    for i, (level, name, count, total, path) in zip(range(number), supported_crates):
        print('{:3d} {:.2f} {:2d} {:2d} {:20s} {}'.format(
            i, level, count, total, name, path.split('rust-rosetta/tasks')[1]))


def show_problematic_reasons(results):
    reasons = compute_reasons(results)
    reason_counts = [(count, reason) for reason, count in reasons.items()]
    reason_counts.sort()
    reason_counts.reverse()
    for count, reason in reason_counts:
        print(count, reason)


def show_opportunistic_reasons(results, count=1):
    """
    Find all functions that cannot be verified because of only one
    restriction and show for each restriction how many functions are
    blocked by it.
    """
    counts = {}
    for example in results:
        for function in example['functions']:
            restrictions = function['procedure']['restrictions']
            if len(restrictions) <= count and restrictions:
                pairs = []
                for restriction in restrictions:
                    for key, value in restriction.items():
                        pairs.append((key, value))
                pairs.sort()
                pairs = tuple(pairs)
                try:
                    counts[pairs] += 1
                except KeyError as e:
                    counts[pairs] = 1
    reason_counts = [(count, reason) for reason, count in counts.items()]
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

    # show_reason(results, 'mutable return type')
    # show_reason(results, 'immutable return type')

    ignore_reason(results, 'mutable return type')
    ignore_reason(results, 'immutable return type')

    # show_opportunistic_reasons(results, count=1)

    ignore_reason(results, 'lifetime parameters are partially supported')
    ignore_reason(results, 'mutable arguments are partially supported')
    ignore_reason(results, 'generic type parameters are not supported')
    ignore_reason(results, '`slice` types are not supported')
    ignore_reason(results, 'shared references are partially supported')


    ignore_reason(results, 'references inside data structures are partially supported')
    # ignore_reason(results, '`str` types are ignored')
    ignore_reason(results, 'cast operations are not supported')
    ignore_reason(results, 'function type parameters are not supported')
    ignore_reason(results, 'length operations are not supported')
    ignore_reason(results, 'index operations are not supported')

    # Chars:
    ignore_reason(results, '`char` types are not supported position=adt')
    ignore_reason(results, '`char` types are not supported position=mir_local')
    ignore_reason(results, '`char` types are not supported position=operand')
    ignore_reason(results, '`char` types are not supported position=input')
    ignore_reason(results, '`char` types are not supported position=output')
    ignore_reason(results, '`char` types are not supported position=mir_output')
    ignore_reason(results, '`char` types are not supported position=mir_arg')
    ignore_reason(results, '`char` types are not supported position=assign')
    ignore_reason(results, 'indices generated by slice patterns are not supported')

    drop_small_functions(results, 5)

    show_support_status(results, 50)

#   show_problematic_reasons(results)



if __name__ == '__main__':
    main()
