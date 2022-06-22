.PHONY: all
all:
	./.venv/bin/papermill ./Analysis.ipynb -p commit 9c34441 \
			--no-report-mode /dev/null

clean:
	${RM} trivial-*.log solved_pivot_table.tex *.pdf
