#!/usr/bin/env python3
import os
from pathlib import Path
import re
import fileinput
from collections import defaultdict, namedtuple
import csv
import sys

Result = namedtuple("Result", ["file_name", "sat_status", "runtime"])
file_names = sys.argv[1:]

LINE_RE = re.compile(
    r"^==== (?P<file_name>.*?): (?P<sat_status>sat|unsat|timeout.*ms) run: (?P<runtime>[0-9\.]+)s parse: .*====$"
)


def parse_lines(lines):
    for line in lines:
        match = LINE_RE.match(line)
        if not match:
            continue
        sat_status = match.group("sat_status")
        runtime = (
            float(match.group("runtime"))
            if not "timeout" in sat_status
            else float("inf")
        )
        yield Result(
            match.group("file_name"),
            sat_status,
            runtime,
        )

def fmt_result(result: Result):
    if "timeout" in result.sat_status:
       return "-"
    else:
        return f"{result.sat_status:>5} in {result.runtime:02.03f}"



instance_to_results = defaultdict(dict)

for log_name in file_names:
    with open(log_name) as log:
        for result in parse_lines(log):
            instance_to_results[result.file_name][log_name] = result

print("\t\t".join(["instance", *file_names]))

for instance, results in instance_to_results.items():
    print(
        "\t\t".join(
            [
                str(Path(instance).relative_to(os.getcwd())),
                *[fmt_result(results[solver]) for solver in file_names],
            ]
        )
    )
