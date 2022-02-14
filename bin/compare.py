#!/usr/bin/env python3
import sys
import re
from collections import Counter, defaultdict

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
        sat_status = match.group("sat_status")
        results[match.group("file_name")] = (
            sat_status,
            float(match.group("runtime"))
            if not "timeout" in sat_status
            else float("inf"),
        )
    return results


def classify_outcome(left_runtime, right_runtime):
    runtime_diff = left_runtime - right_runtime
    runtime_difference_is_large = (
        abs(runtime_diff) / abs(max(left_runtime, right_runtime))
    ) >= 0.10 and abs(runtime_diff) > 1.0

    if runtime_difference_is_large:
        # print(
        #    f"I: {instance} runtime: {left_runtime} vs {right_runtime}: diff {runtime_diff}"
        # )
        if runtime_diff < 0:
            return "left wins"
        else:
            return "right wins"
    else:
        return "draws"


with open(left) as left, open(right) as right:
    lefts = parse_lines(left)
    rights = parse_lines(right)

common_keys = set(lefts.keys()).intersection(rights.keys())

if not lefts.keys() == rights.keys():
    different_keys = set(lefts.keys()).symmetric_difference(set(rights.keys()))
    different_keys_str = (
        ", ".join(list(different_keys)[:5]) + f" ...and {len(different_keys) - 5} more"
        if len(different_keys) > 5
        else ", ".join(different_keys)
    )
    print(f"W: The following files are not in both sets:\n{different_keys_str}")
    print(f"I: Proceeding with the {len(common_keys)} common instance(s)...")


nr_different = 0
outcomes = defaultdict(Counter)


for instance in common_keys:
    left_status, left_runtime = lefts[instance]
    right_status, right_runtime = rights[instance]

    instance_type = "unknown"

    if "timeout" in left_status and "timeout" in right_status:
        outcomes[instance_type]["both timeout"] += 1
        print(f"W: No ground truth for {instance}: both timed out!")
        continue

    results = {s for s in [left_status, right_status] if not "timeout" in s}

    if len(results) == 1:
        # At least one solver did not time out and reported a status: we assume
        # it is correct and use that to classify the instance.
        instance_type = list(results)[0]
    else:
        # The solvers both came to a conclusion, but don't agree: we can't trust
        # the numbers.
        print(f"W: different outcomes {left_status}/{right_status} for {instance}!")
        nr_different += 1
        continue

    # Now we know: at least one solver has a solution.
    outcomes[instance_type][classify_outcome(left_runtime, right_runtime)] += 1

print()
print("======= Summary =======")
print(f"\nDifferent outcomes: {nr_different}\n")
for outer_label, counts in outcomes.items():
    print(f"## {outer_label}")
    inner_label_maxlen = max(len(l) for l in counts.keys()) + 4
    for inner_label, count in counts.most_common():
        print(f"{inner_label:{inner_label_maxlen}} {count}")
    print()
