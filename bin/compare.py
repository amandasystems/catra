#!/usr/bin/env python3
import sys
import re

left = sys.argv[1]
right = sys.argv[2]
LINE_RE = re.compile(
    r"^==== (?P<file_name>.*?): (?P<sat_status>sat|unsat|timeout.*ms) run: (?P<runtime>[0-9\.]+)s parse: .*====$"
)


def parse_lines(lines):
    results = dict()

    for line in lines:
        match = LINE_RE.match(line)
        if not match:
            continue
        results[match.group("file_name")] = (
            match.group("sat_status"),
            float(match.group("runtime")),
        )
    return results


with open(left) as left, open(right) as right:
    lefts = parse_lines(left)
    rights = parse_lines(right)

if not lefts.keys() == rights.keys():
    different_keys = set(lefts.keys()).symmetric_difference(set(rights.keys()))
    different_keys_str = (
        ", ".join(list(different_keys)[:5]) + f" ...and {len(different_keys) - 5} more"
        if len(different_keys) > 5
        else ", ".join(different_keys)
    )
    print(
        f"The following {len(different_keys)} files are not in both sets: {different_keys_str}"
    )

nr_same = 0
nr_different = 0
nr_timeout = 0
nr_left_wins = 0
nr_right_wins = 0
nr_draws = 0

common_keys = set(lefts.keys()).intersection(rights.keys())
for instance in common_keys:
    left_status, left_runtime = lefts[instance]
    right_status, right_runtime = rights[instance]
    if "timeout" in left_status or "timeout" in right_status:
        nr_timeout += 1
        if "timeout" in left_status and not "timeout" in right_status:
            print(f"right could solve {instance}, left timed out!")
            nr_right_wins += 1
        if "timeout" in right_status and not "timeout" in left_status:
            print(f"left could solve {instance}, right timed out!")
            nr_left_wins += 1
        continue
    if not left_status == right_status:
        print(f"{instance} differs: {left_status} != {right_status}")
        nr_different += 1
    else:
        nr_same += 1
        runtime_diff = left_runtime - right_runtime
        runtime_difference_is_large = (
            abs(runtime_diff) / abs(max(left_runtime, right_runtime))
        ) >= 0.5 and runtime_diff
        if runtime_difference_is_large:
            print(
                f"{instance} runtime: {left_runtime} vs {right_runtime}: diff {runtime_diff}"
            )
            if runtime_diff < 0:
                nr_left_wins += 1
            else:
                nr_right_wins += 1
        else:
            nr_draws += 1
print(f"nr different: {nr_different}, nr same: {nr_same}, nr timeout: {nr_timeout}")
print(f"left wins: {nr_left_wins}, nr draws: {nr_draws}, right wins: {nr_right_wins}")
