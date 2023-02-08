#!/bin/bash

timeout=120000
logfile=regressions.log
trap "echo '\nExited!'; exit;" SIGINT SIGTERM

iteration=0

while true;
do
  echo "Looking for bug"
  for instance in $(find regressions -type f)
  do
    ((iteration++))
    printf "."
    CATRA_TRACE=true ./bin/catra solve-satisfy  --timeout ${timeout} "${instance}" &> ${logfile};
    if $(grep -q '====.* unsat' ${logfile});
    then
      echo "\nFound bug with ${instance} after ${iteration} iterations!"
      exit
    fi
  done
done
