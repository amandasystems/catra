#!/bin/sh
CURRENT_VERSION=$(sbt -Dsbt.supershell=false -error "print validator/version")
mkdir -p logs
sbt "validator/run $@" | tee logs/${CURRENT_VERSION}.validation.log
