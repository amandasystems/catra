#!/bin/sh

INSTANCE_PATH="find-image"
TIMEOUT_MS="120000"

CMD_BASELINE="../bin/catra find-image \
  --timeout ${TIMEOUT_MS} \
  --backend baseline \
  --no-check-term-sat \
  --no-check-intermediate-sat \
  --print-decisions \
  --no-eliminate-quantifiers ${INSTANCE_PATH} > baseline-find-image.log"

CMD_LAZY="../bin/catra find-image \
  --timeout ${TIMEOUT_MS} \
  --print-decisions \
  --backend lazy ${INSTANCE_PATH} > lazy-find-image.log"

#parallel -j1 ::: "${CMD_LAZY}" "${CMD_BASELINE}"
eval "${CMD_LAZY}"
eval "${CMD_BASELINE}"
