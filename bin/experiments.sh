#!/bin/bash

CURRENT_VERSION=$(git rev-parse --short HEAD)
ALL_ARGS="$*"
PARALLEL_JOBS=3

export ALL_ARGS CURRENT_VERSION

run_solver() {
  ./bin/catra solve-satisfy --backend "$1" "$ALL_ARGS" >"${CURRENT_VERSION}-$1.log"
}
export -f run_solver

echo "${CURRENT_VERSION}: Executing ${PARALLEL_JOBS} experiments in parallel"
parallel -j ${PARALLEL_JOBS} run_solver ::: lazy nuxmv baseline
