#!/bin/sh

CATRA_TRACE=true ./bin/catra solve-satisfy $@ 2> log1.log
CATRA_TRACE=true ./bin/catra solve-satisfy $@ 2> log2.log
diff log1.log log2.log | head -10
