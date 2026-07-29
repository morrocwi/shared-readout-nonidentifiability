COQC ?= coqc
LATEX ?= pdflatex

.PHONY: all verify formal paper clean

all: verify

verify: formal paper

formal:
	$(COQC) -q CoreTheorem.v
	@! grep -nE '^[[:space:]]*(Axiom|Parameter|Conjecture|Admitted)([[:space:]]|\.)' CoreTheorem.v

paper:
	$(LATEX) -interaction=nonstopmode -halt-on-error -output-directory=paper paper/main.tex
	$(LATEX) -interaction=nonstopmode -halt-on-error -output-directory=paper paper/main.tex
	@! grep -E 'Overfull \\hbox|Overfull \\vbox' paper/main.log

clean:
	rm -f CoreTheorem.vo CoreTheorem.vok CoreTheorem.vos CoreTheorem.glob
	rm -f paper/main.aux paper/main.log paper/main.out paper/main.toc
