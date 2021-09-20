DEPS=$(latexmk -deps main.tex)
dotfiles = $(wildcard *.dot)
all_automata = $(patsubst %.dot,%.pdf,${dotfiles})



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