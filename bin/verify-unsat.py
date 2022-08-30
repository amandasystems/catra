#!/usr/bin/env python3
import fileinput
import pathlib
import re
import subprocess
import sys

VERIFY_WITH_BACKEND = "nuxmv"
LINE_RE = r'^==== (?P<instance>.*?): unsat.*====$'
SAT_UNSAT_RE = re.compile(
    r"^==== (?P<file_name>.*?): (?P<sat_status>sat|unsat|timeout.*ms) run: (?P<runtime>[\d.]+)s parse: .*===="
)
TARGET_DIR = pathlib.Path("verification")
CATRA = "./bin/catra"

log = "".join(fileinput.input())

def run_catra(instance):
    res = subprocess.run(
        [
            CATRA,
            "solve-satisfy",
            "--backend",
            VERIFY_WITH_BACKEND,
            #"--timeout",
            #str(TIMEOUT_S * 1000),
            instance,
        ],
        check=True,
        encoding="utf8",
        capture_output=True,
    )
    result = SAT_UNSAT_RE.match(res.stdout)
    if res.stderr:
        print(res.stderr)
    if not result:
        return "unknown"
    return result.group("sat_status"), res.stdout


def second_opinion_agrees(instance_file):
    (sat_status, log) = run_catra(instance_file)
    if sat_status == "sat":
        return "agree"
    if sat_status == "unsat":
        return "disagree"
    return "unknown"

matches = re.finditer(LINE_RE, log, re.MULTILINE)
instances = [pathlib.Path(match.group("instance")) for match in matches]

for instance_file in instances:
    sat_status, log = run_catra(instance_file)
    if sat_status == "sat":
        print(f"E: {VERIFY_WITH_BACKEND} disagrees for {instance_file} >>", 
                file=sys.stderr)
        print(log, file=sys.stderr)
    elif sat_status == "unsat":
        print(f"I: {VERIFY_WITH_BACKEND} argees for {instance_file}")
    else:
        print(
            f"W: {VERIFY_WITH_BACKEND} unknown status for {instance_file}:", file=sys.stderr
        )
        print(log, file=sys.stderr)
