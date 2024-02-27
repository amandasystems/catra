#!/bin/bash
set -x
CURRENT_VERSION=$(sbt -Dsbt.supershell=false -error "print benchmark/version")
RESTART_AFTER=10
LOGFILE="logs${CATRA_TAG}/catra-${CURRENT_VERSION}.experiments.log"
JARFILE="benchmark/target/scala-2.13/catra-benchmark-assembly-${CURRENT_VERSION}.jar"

mkdir -p "logs${CATRA_TAG}"

echo "" > $LOGFILE

echo "${CURRENT_VERSION}: Executing experiments in parallel, logging to ${LOGFILE}"
find "$@" -type f | xargs -n $RESTART_AFTER -- \
  java -XX:MaxRAMPercentage=90.0 -jar "$JARFILE" | tee -a "$LOGFILE"

echo "Done with all experiments!" >> "$LOGFILE"
