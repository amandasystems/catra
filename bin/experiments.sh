#!/bin/bash

CURRENT_VERSION=$(sbt -Dsbt.supershell=false -error "print benchmark/version")
RESTART_AFTER=10
LOGFILE="logs/catra-${CURRENT_VERSION}.experiments.log"

echo "${CURRENT_VERSION}: Executing experiments in parallel, logging to ${LOGFILE}"
find $@ -type f | xargs -n $RESTART_AFTER -- \
  java -XX:MaxRAMPercentage=90.0 -jar runner/target/scala-2.13/catra-benchmark-assembly-"${CURRENT_VERSION}".jar \
  | tee "$LOGFILE"
