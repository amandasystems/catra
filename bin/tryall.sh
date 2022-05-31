#!/bin/sh

timeout=120000
echo "++++++ Running all solvers +++++++"
for backend in princess nuxmv verma;
do
    echo ${backend}:
    ./bin/catra solve-satisfy --timeout ${timeout} --backend ${backend} $@ > ${backend}.log
done
