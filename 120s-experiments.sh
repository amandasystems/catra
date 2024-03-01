#!/bin/bash
set -x
RESTART_AFTER=10
export CATRA_TIMEOUT=120000
export CATRA_CONFIGS="baseline,lazy"
export CATRA_THREADS=1
LOGFILE="${CATRA_CONFIGS}-catra-${RESTART_AFTER}.${CATRA_TIMEOUT}.log"
JARFILE=$(ls -1t benchmark/target/scala-2.13/*.jar | head -1)

echo "" > "$LOGFILE"

find 120s-experiments.d -type f | xargs -n $RESTART_AFTER -- \
  java -Xmx10G -jar "$JARFILE" | tee -a "$LOGFILE"

echo "Done with all experiments!" >> "$LOGFILE"
