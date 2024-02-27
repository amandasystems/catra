#!/bin/sh

CATRA_TAG=".cactus" CATRA_TIMEOUT="120000" ./bin/experiments.sh ../parikh-plus-selected
CATRA_TIMEOUT="30000" CATRA_CONFIGS="nuxmv,baseline,lazy" ./bin/experiments.sh ../deduped-benchmarks
