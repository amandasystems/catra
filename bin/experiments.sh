#!/bin/bash

CURRENT_VERSION=$(git rev-parse --short HEAD)
RESTART_AFTER=10
LOGFILE="${CURRENT_VERSION}.experiments.log"

echo "${CURRENT_VERSION}: Executing experiments in parallel, logging to ${LOGFILE}"
find $@ -type f | xargs -n $RESTART_AFTER -- \
  java -XX:MaxRAMPercentage=90.0 -jar runner/target/scala-2.13/catra-benchmark-assembly-0.1.0-SNAPSHOT.jar \
  | tee $LOGFILE 
