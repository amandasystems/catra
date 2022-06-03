#!/usr/bin/env python3

import sys
from pathlib import Path
import shutil
import os

if len(sys.argv) != 2:
    print("Usage: {sys.argv[0]} target directory < files-to-copy")
    sys.exit(1)

target = Path(sys.argv[1])


for filepath in sys.stdin:
    filepath = Path(filepath.strip())
    relative_path = filepath.relative_to(os.getcwd()) if filepath.is_relative_to(os.getcwd()) else filepath
    target_file = target / relative_path
    target_file.parent.mkdir(parents=True, exist_ok=True)
    try:
        shutil.copyfile(relative_path, target_file)
        print(target_file)
    except FileNotFoundError:
        print(f"W: file does not exist {relative_path}", file=sys.stderr)
