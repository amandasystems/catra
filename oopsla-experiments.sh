#!/bin/sh

# 120s benchmarks:
CATRA_TIMEOUT=120000\
    CATRA_CONFIGS="nuxmv,lazy,lazy-no-clauselearning-no-restarts,lazy-eager-1,lazy-lazy-200" \
    CATRA_THREADS=4 ./bin/experiments.sh 120s-experiments.d
CATRA_TIMEOUT=120000 CATRA_CONFIGS=baseline CATRA_THREADS=2 ./bin/experiments.sh 120s-experiments.d

# 30s benchmarks:
CATRA_TIMEOUT=30000 CATRA_CONFIGS=lazy,nuxmv CATRA_THREADS=6 ./bin/experiments.sh deduped-benchmarks
CATRA_TIMEOUT=30000 CATRA_CONFIGS=baseline CATRA_THREADS=2 ./bin/experiments.sh deduped-benchmarks
