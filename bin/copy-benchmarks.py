#!/usr/bin/env python3

import sys
from pathlib import Path
import shutil

if len(sys.argv) == 3:
    base = Path(sys.argv[1])
    target = Path(sys.argv[2])
elif len(sys.argv) == 2:
    base = Path(".")
    target = Path(sys.argv[1])
else:
    print(f"Usage: {sys.argv[0]} [benchmark base path] target")
    sys.exit(1)

with open(target / "manifest.txt", "w") as manifest_fp:
    for i, filepath in enumerate(sys.stdin):
        instance_path = base / filepath.strip()
        target_fn = f"{i}.par"
        target_path = target / target_fn
        shutil.copyfile(instance_path, target_path)
        manifest_fp.write(f"{target_fn}: {instance_path}\n")
