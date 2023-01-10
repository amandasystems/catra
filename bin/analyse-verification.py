#!/usr/bin/env python3

import os.path
import os
from sys import argv, exit
from pathlib import Path

outs = []
errs = []
EXIT_OK = 0
EXIT_ERRORS = 1

if len(argv) != 2:
    print(f"Usage: {argv[0]} [result directory]")
    exit(EXIT_ERRORS)

for dirpath, _, files in os.walk(Path(argv[1])):
    for f in files:
        if f not in ["stderr", "stdout"]:
            continue
        target = outs if f == "stdout" else errs
        target.append(Path(os.path.join(dirpath, f)))

def count_validation_errors(stdout_log):
    nr_validation_errors = 0
    with stdout_log.open() as lines:
        for line in lines:
            if "error: nuXmv disagrees with solution" in line:
                nr_validation_errors += 1
    return nr_validation_errors

found_errors = False
for f in outs:
    nr_errors = count_validation_errors(f)
    if nr_errors:
        found_errors = True
        print(f"{f.parent}: {nr_errors}")

if not found_errors:
    print("No validation errors in any log!")
    print(f"Analysed the following files: {', '.join([str(f) for f in outs])}")
    exit(EXIT_OK)
else:
    exit(EXIT_ERRORS)
