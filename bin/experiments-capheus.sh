#!/bin/sh
CURRENT_VERSION=$(git rev-parse --short HEAD)
JARFILE=./target/scala-2.13/uuverifiers/catra-assembly-${CURRENT_VERSION}.jar
RAM_ALLOC=4g
NR_THREADS=10

git reset --hard
git pull
sbt assembly

parallel -j$NR_THREADS --header : \
  --eta --results $CURRENT_VERSION.capheus java -jar -Xmx${RAM_ALLOC} $JARFILE \
  solve-satisfy --timeout 60000 \
  --backend {backend} {chunk} \
  ::: backend baseline nuxmv lazy ::: chunk chunks/chunk-*
