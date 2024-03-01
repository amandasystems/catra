#!/bin/bash
set -x

LOGFILE="baseline-120s.log"
JARFILE=$(ls -1t target/scala-2.13/uuverifiers/*.jar | head -1)

echo "" > "$LOGFILE"

for instance in 120s-experiments.d/*
do
    timeout --signal 9 --preserve-status 300s \
    java -Xmx20G -jar $JARFILE \
    solve-satisfy --backend baseline \
                  --timeout 120000 $instance $instance
done | tee -a "$LOGFILE"


echo "Done with all experiments!" >> "$LOGFILE"