#!/usr/bin/env python3
import re
import fileinput
from collections import namedtuple
import csv
import sys

Result = namedtuple("Result", ["file_name", "sat_status", "runtime"])

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


writer = csv.writer(sys.stdout)
writer.writerow(["instance", "status", "runtime"])
writer.writerows(parse_lines(fileinput.input()))
