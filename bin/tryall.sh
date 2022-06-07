#!/bin/sh

timeout=2000
echo "++++++ Running all solvers +++++++"
for backend in lazy nuxmv baseline;
do
    echo ${backend}:
    ./bin/catra solve-satisfy --timeout ${timeout} --backend ${backend} $@ > ${backend}.log
done
