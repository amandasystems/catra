#!/usr/bin/env python3
import random
import sys
from pathlib import Path
import shutil
import os

if len(sys.argv) != 3:
    print("Usage: {sys.argv[0]} nr splits target directory < files-to-copy")
    sys.exit(1)

nr_chunks = int(sys.argv[1])
target = Path(sys.argv[2])

paths_to_split = [Path(filepath.strip()) for filepath in sys.stdin if filepath.strip()]
random.shuffle(paths_to_split)
chunk_size = len(paths_to_split) // nr_chunks


def chunker(seq, size):
    return (seq[pos:pos + size] for pos in range(0, len(seq), size))


for i, file_chunk in enumerate(chunker(paths_to_split, chunk_size)):
    for filepath in file_chunk:
        relative_path = filepath.relative_to(os.getcwd()) if filepath.is_relative_to(os.getcwd()) else filepath
        target_file = target / f"chunk-{i}" / relative_path
        target_file.parent.mkdir(parents=True, exist_ok=True)
        try:
            shutil.copyfile(relative_path, target_file)
            print(target_file)
        except FileNotFoundError:
            print(f"W: file does not exist {relative_path}", file=sys.stderr)
