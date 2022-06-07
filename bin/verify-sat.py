#!/usr/bin/env python3
import fileinput
import os
import pathlib
import re
import subprocess

VERIFY_WITH_BACKEND = "lazy"
LINE_RE = r"^==== (?P<instance>.*?): sat run: [0-9\.]+s parse: .*====$\n(?P<registers>(.+ = \d+$\n)+)"
SAT_UNSAT_RE = re.compile(
    r"^==== (?P<file_name>.*?): (?P<sat_status>sat|unsat|timeout.*ms) run: (?P<runtime>[0-9\.]+)s parse: .*===="
)
TARGET_DIR = pathlib.Path("verification")
TIMEOUT_S = 60
CATRA = "./bin/catra"

log = "".join(fileinput.input())


def verifier_from_witness(instance_file, assignments):
    extra_constraint = " && ".join([f"{r} = {v}" for r, v in assignments.items()])
    with instance_file.open() as fp:
        return "\n".join([*[line for line in fp], f"constraint {extra_constraint};\n"])


def dump_verifier(source, derived_from):
    target_file = TARGET_DIR / derived_from.relative_to(os.getcwd())
    target_file.parent.mkdir(parents=True, exist_ok=True)
    with target_file.open("w") as fp:
        fp.writelines(source)
    return target_file


def run_catra(instance):
    res = subprocess.run(
        [
            CATRA,
            "solve-satisfy",
            "--backend",
            VERIFY_WITH_BACKEND,
            "--timeout",
            str(TIMEOUT_S * 1000),
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
    return result.group("sat_status")


def second_opinion_agrees(instance_file, witness):
    verifier = verifier_from_witness(instance_file, witness)
    verifier_filename = dump_verifier(verifier, instance_file)
    sat_status = run_catra(verifier_filename)
    if sat_status == "sat":
        return "agree"
    if sat_status == "unsat":
        return "disagree"
    return "unknown"


matches = re.finditer(LINE_RE, log, re.MULTILINE)
instances = dict()
for match in matches:
    instance = pathlib.Path(match.group("instance"))
    instances[instance] = dict()
    for assignment in match.group("registers").split("\n"):
        if not assignment:
            continue
        lhs, rhs = assignment.split(" = ", maxsplit=2)
        rhs = int(rhs)
        instances[instance][lhs] = rhs

for instance_file, witness in instances.items():
    outcome = second_opinion_agrees(instance_file, witness)
    if outcome == "agree":
        print(f"Verified {instance_file}")
    elif outcome == "unknown":
        print(f"W: {VERIFY_WITH_BACKEND} timed out verifying {instance_file}")
    else:
        print(outcome)
        print(
            f"E: {VERIFY_WITH_BACKEND} disagrees with assignment for {instance_file}:"
        )
        for lhs, rhs in witness.items():
            print(f"{lhs} = {rhs}")
