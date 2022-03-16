DEPS=$(latexmk -deps main.tex)
dotfiles = $(wildcard *.dot)
all_automata = $(patsubst %.dot,%.pdf,${dotfiles})
current_version = $(shell git rev-parse --short HEAD)
TIMEOUT_MS = 30000
EXPERIMENT_DIR = ../parikh-plus
#NR_EXPERIMENTS = 60

all: ${all_automata} montage.png

montage.png: ${all_automata}
	magick montage -tile x2 \
								-label %t \
								-border 2 \
								-bordercolor black \
								-geometry +4+4 \
								${all_automata} $@


%.pdf: %.dot
	dot -Tpdf -o $@ $<

# -Earrowsize=0.5 -Efontsize=9.0

clean:
	${RM} ${all_automata}
	latexmk -c

veryclean:
	${MAKE} clean
	${RM} *.dot
	${RM} montage.png
	${RM} trace.tex
	${RM} trace-*


trace.pdf: trace.tex ${DEPS} ${all_automata}
	latexmk -pdf $<

.PHONY: experiments
experiments:
	./bin/catra solve-satisfy --backend nuxmv \
				--timeout ${TIMEOUT_MS} \
				> ${current_version}-nuxmv.log \
				basket
	./bin/catra solve-satisfy --timeout ${TIMEOUT_MS} \
				> ${current_version}-catra.log \
				basket


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
