#!/bin/sh
CURRENT_VERSION=$(sbt -Dsbt.supershell=false -error "print validator/version")

sbt "validator/run $@" | tee logs/${CURRENT_VERSION}.validation.log
