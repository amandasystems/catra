#!/bin/bash
set -x
JARFILE=$(ls -1t benchmark/target/scala-2.13/*.jar | head -1)
export CATRA_TIMEOUT=$CATRA_TIMEOUT
export CATRA_CONFIGS=$CATRA_CONFIGS
export CATRA_THREADS=$CATRA_THREADS
RESTART_AFTER=$CATRA_THREADS
LOGFILE="logs/$(basename ${JARFILE} .jar).experiments.configs=${CATRA_CONFIGS}.parallel=${RESTART_AFTER}.timeout=${CATRA_TIMEOUT}.log"

mkdir -p "logs"

echo "" > $LOGFILE

echo "${CURRENT_VERSION}: Executing experiments in parallel, logging to ${LOGFILE}"
find "$@" -type f | xargs -n $RESTART_AFTER -- \
  java -Xmx100G -jar "$JARFILE" | tee -a "$LOGFILE"

echo "Done with all experiments!" >> "$LOGFILE"
