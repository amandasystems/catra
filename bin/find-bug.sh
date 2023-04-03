#!/bin/bash

timeout=30000
logfile=regressions.log
trap "printf '\nExited!\n'; exit;" SIGINT SIGTERM

iteration=0

echo "Looking for bug"
while true;
do
  for instance in bug-proof-cert.par
  do
    ((iteration++))
    ./bin/catra solve-satisfy  --print-decisions --timeout ${timeout} "${instance}" &> ${logfile};
    if $(grep -q '====.* unsat' ${logfile});
    then
      printf "!"
      cp ${logfile} bug-${iteration}.log
    fi
    if $(grep -q '====.* timeout' ${logfile}); then
      printf "t"
    else
      printf "."
    fi
    if $(grep -q '====.* error' ${logfile}); then
      printf "e"
      cp ${logfile} error-${iteration}.log
    fi
  done
done
