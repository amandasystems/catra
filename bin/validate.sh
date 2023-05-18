#!/bin/sh
set -x
CURRENT_VERSION=$(sbt -Dsbt.supershell=false -error "print validator/version")
LOGFILE="logs/${CURRENT_VERSION}.validation.log"
JARFILE="validator/target/scala-2.13/catra-validate-assembly-${CURRENT_VERSION}.jar"

mkdir -p logs
java -XX:MaxRAMPercentage=90.0 -jar "$JARFILE" "$@" | tee $LOGFILE