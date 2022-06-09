#!/bin/sh

INVOCATIONS=$(perl -E 'say "experiments/trivial.par " x 15')

for backend in lazy nuxmv baseline;
do
  ./bin/catra solve-satisfy --backend ${backend} $INVOCATIONS > experiments/trivial-${backend}.log
done
