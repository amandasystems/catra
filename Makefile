current_version = $(shell git rev-parse --short HEAD)
TIMEOUT_MS = 30000
EXPERIMENT_DIR = parikh-plus

.PHONY: all
all: experiments

clean:
	sbt clean

veryclean:
	${MAKE} clean
	${RM} *.dot
	${RM} montage.png
	${RM} trace.tex
	${RM} trace-*


.PHONY: experiments
experiments:
	sbt assembly
	./bin/experiments.sh --timeout ${TIMEOUT_MS} basket


.PHONY: smoke-test
smoke-test:
	sbt assembly
	find experiments -type f \
		| shuf \
		| head -n 10 \
		| xargs --\
			 ./bin/catra solve-satisfy \
			 --timeout 500 > /dev/null
	find experiments -type f \
		| shuf \
		| head -n 10 \
		| xargs --\
			 ./bin/catra solve-satisfy \
			 --backend nuxmv \
			 --timeout 500 > /dev/null
