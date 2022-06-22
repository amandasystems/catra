#!/bin/sh

for limit in 0 2 5 10 100 1000
do
  /usr/bin/time -o time-$limit.log ./bin/catra solve-satisfy --timeout 30000 --nr-unknown-to-start-materialise  $limit basket > $limit-basket.log
done
