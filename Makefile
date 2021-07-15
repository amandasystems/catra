dotfiles = $(wildcard *.dot)
all_automata = $(patsubst %.dot,%.png,${dotfiles})



all: ${all_automata} montage.png

montage.png: ${all_automata}
	magick montage -tile x2 \
								-label %t \
								-border 2 \
								-bordercolor black \
								-geometry +4+4 \
								${all_automata} $@


%.png: %.dot
	dot -Tpng -o $@ $<

# -Earrowsize=0.5 -Efontsize=9.0

clean:
	${RM} ${all_automata}

veryclean:
	${MAKE} clean
	${RM} *.dot
	${RM} montage.png
