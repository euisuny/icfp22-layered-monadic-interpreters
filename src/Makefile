.PHONY: clean all coq test tests examples tutorial install uninstall depgraph for-dune

COQPATHFILE=$(wildcard _CoqPath)

build: coq

include common.mk

all:
	# Build the library before tests
	$(MAKE) coq
	$(MAKE) tutorial
	$(MAKE) test

install: Makefile.coq coq
	$(MAKE) -f $< $@

uninstall: Makefile.coq
	$(MAKE) -f $< $@

test: examples tests

tests:
	$(MAKE) -C tests
	$(MAKE) -C tutorial test

examples:
	$(MAKE) -C examples

tutorial:
	$(MAKE) -C tutorial

clean: clean-coq
	$(RM) _CoqProject
	$(MAKE) -C tests clean
	$(MAKE) -C examples clean
	$(MAKE) -C tutorial clean

_CoqProject: $(COQPATHFILE) _CoqConfig Makefile
	@ echo "# Generating _CoqProject"
	@ rm -f _CoqProject
	@ echo "# THIS IS AN AUTOMATICALLY GENERATED FILE" >> _CoqProject
	@ echo "# PLEASE EDIT _CoqConfig INSTEAD" >> _CoqProject
	@ echo >> _CoqProject
ifneq ("$(COQPATHFILE)","")
	@ echo "# including: _CoqPath"
	@ cat _CoqPath >> _CoqProject
	@ echo >> _CoqProject
endif
	@ echo "# including: _CoqConfig"
	@ cat _CoqConfig >> _CoqProject

COQDEP=coqdep
DEPS_DOT=deps.dot
DEPS_OUT=deps.jpg

depgraph:
	$(COQDEP) -dumpgraph $(DEPS_DOT) $(shell cat _CoqConfig) > /dev/null 2>&1
	sed 's%\("theories/\([^"]*\)/\([^"/]*\)"\[label="\)%\1\2/\\n%' -i $(DEPS_DOT)
	dot $(DEPS_DOT) -Tjpg -o$(DEPS_OUT)

# EXTRA_DIR:=extra
# COQDOCFLAGS:= \
#   --external 'http://ssr2.msr-inria.inria.fr/doc/ssreflect-1.5/' Ssreflect \
#   --external 'http://ssr2.msr-inria.inria.fr/doc/mathcomp-1.5/' MathComp \
#   --toc --toc-depth 2 --html --interpolate \
#   --index indexpage --no-lib-name --parse-comments \
#   --with-header $(EXTRA_DIR)/header.html --with-footer $(EXTRA_DIR)/footer.html
# export COQDOCFLAGS
# COQMAKEFILE:=Makefile.coq
# COQ_PROJ:=_CoqProject
# VS:=$(wildcard *.v)
# VS_IN_PROJ:=$(shell grep .v $(COQ_PROJ))

# ifeq (,$(VS_IN_PROJ))
# VS_OTHER := $(VS)
# else
# VS := $(VS_IN_PROJ)
# endif

# all:
# 	html

# clean: $(COQMAKEFILE)
# 	@$(MAKE) -f $(COQMAKEFILE) $@
# 	rm -f $(COQMAKEFILE)

# html: $(COQMAKEFILE) $(VS)
# 	rm -fr html
# 	@$(MAKE) -f $(COQMAKEFILE) $@
# 	cp $(EXTRA_DIR)/resources/* html
# 	cp $(EXTRA_DIR)/index.html html

# $(COQMAKEFILE): $(COQ_PROJ) $(VS)
# 		coq_makefile -f $(COQ_PROJ) $(VS_OTHER) -o $@

# %: $(COQMAKEFILE) force
# 	@$(MAKE) -f $(COQMAKEFILE) $@
# force $(COQ_PROJ) $(VS): ;

# .PHONY: clean all force
