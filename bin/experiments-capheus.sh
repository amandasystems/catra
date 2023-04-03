#!/bin/sh
JARFILE=./target/scala-2.13/uuverifiers/catra-assembly-0.1.0-SNAPSHOT.jar
CURRENT_VERSION=$(git rev-parse --short HEAD)
RAM_ALLOC=10g
NR_THREADS=8

#git reset --hard
#git pull
sbt assembly

parallel -j$NR_THREADS --header : \
  --eta --results $CURRENT_VERSION.capheus java -jar -Xmx${RAM_ALLOC} $JARFILE \
  solve-satisfy --timeout 60000 \
  --backend {backend} {chunk} \
  ::: backend baseline nuxmv lazy ::: chunk chunks/chunk-*
