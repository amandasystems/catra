#!/bin/bash

SERVERS="-S 2/lc2 -S 2/lc3 -S 2/lc5 -S 2/lc6"
BASE_COMMAND='$HOME/jdk-11.0.15+10/bin/java -Xmx2g -jar $HOME/catra.jar solve-satisfy --timeout 5000 --backend baseline {}'

parallel --bar --eta -j8 $SERVERS $BASE_COMMAND ::: experiments/chunk-*
