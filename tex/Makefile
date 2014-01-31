.PHONY: refresh once force all clean

all: main.pdf

error.pdf: error.tex
	pdflatex $^

main.pdf: main.tex local.sty
	pdflatex $<
	pdflatex $<

once: main.tex local.sty error.pdf
	pdflatex -halt-on-error $< >/dev/null || cp error.pdf main.pdf

force:
	pdflatex main.tex

refresh:
	while inotifywait -e modify .; do make once; done

clean:
	rm -f *.aux *.log *.ans *.out *.toc *.bbl *.blg *.rev *.pdf
