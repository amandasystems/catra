current_version = $(shell sbt -Dsbt.supershell=false -error "print version")
TIMEOUT_MS = 30000
EXPERIMENT_DIR = parikh-plus

.PHONY: all
all: experiments

.PHONY: catra-experiments.zip
catra-experiments.zip:
	sbt assembly
	sbt benchmark/assembly
	zip catra-experiments.zip \
		-r 120s-experiments.* \
		$(shell ls -1t benchmark/target/scala-2.13/*.jar | head -1)
		$(shell ls -1t target/scala-2.13/uuverifers/*.jar | head -1)
		120s-baseline.sh

catra-${current_version}.zip:
	sbt assembly
	zip catra-${current_version}.zip  bin/catra target/scala-2.13/uuverifiers/catra-assembly-${current_version}.jar	


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
