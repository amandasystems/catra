#!/usr/bin/env python3
import sys
import re

left = sys.argv[1]
right = sys.argv[2]
LINE_RE = re.compile(
    r"^==== (?P<file_name>.*?)(?P<sat_status>sat|unsat|timeout.*ms) run: (?P<runtime>[0-9\.]+)s parse: .*====$"
)


def parse_lines(lines):
    results = dict()

    for line in lines:
        match = LINE_RE.match(line)
        if not match:
            continue
        results[match.group("file_name")] = match.group("sat_status")
    return results


with open(left) as left, open(right) as right:
    lefts = parse_lines(left)
    rights = parse_lines(right)

if not lefts.keys() == rights.keys():
    different_keys = ", ".join(
        set(lefts.keys()).symmetric_difference(set(rights.keys()))
    )
    print(f"The following files are not in both sets: {different_keys}")

nr_same = 0
nr_different = 0
nr_timeout = 0
for instance in lefts.keys():
    if "timeout" in lefts[instance] or "timeout" in rights[instance]:
        nr_timeout += 1
        continue
    if not rights[instance] == lefts[instance]:
        print(f"{instance} differs: {lefts[instance]} != {rights[instance]}")
        nr_different += 1
    else:
        nr_same += 1
print(f"nr different: {nr_different}, nr same: {nr_same}, nr timeout: {nr_timeout}")
