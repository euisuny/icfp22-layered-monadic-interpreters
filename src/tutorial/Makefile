.PHONY: tutorial test clean

tutorial: coq test

coq: _CoqProject


include ../common.mk

_CoqProject:
	cp _CoqProject.make _CoqProject

clean: clean-coq
	rm -f _CoqProject
