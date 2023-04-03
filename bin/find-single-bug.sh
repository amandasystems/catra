#!/bin/bash

timeout=20000
logfile=minimised-regressions-$2.log

./bin/catra solve-satisfy --timeout ${timeout} --print-decisions  "$1" &> ${logfile};
if $(grep -q '====.* unsat' ${logfile});
then
  printf "!"
  cp ${logfile} bug-$2.log
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
