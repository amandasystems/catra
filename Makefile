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
	parallel -j50\%  \
	-X \
	--eta --results "${current_version}/{#}/" \
	java -Xmx8g \
	-jar target/scala-2.13/uuverifiers/catra-assembly-0.1.0-SNAPSHOT.jar \
	solve-satisfy --timeout ${TIMEOUT_MS} ::: basket/*.par
	cat ${current_version}/*/stdout > ${current_version}.log

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
