#!/bin/sh
JARFILE=./target/scala-2.13/uuverifiers/catra-assembly-0.1.0-SNAPSHOT.jar
CURRENT_VERSION=$(git rev-parse --short HEAD)
RAM_ALLOC=4g
NR_THREADS=10

sbt assembly

parallel -j$NR_THREADS --header : \
  --eta --results $CURRENT_VERSION.validation java -jar -Xmx${RAM_ALLOC} $JARFILE \
  solve-satisfy --timeout 60000 \
  --backend lazy --cross-validate {chunk} \
  ::: chunk chunks/chunk-*
