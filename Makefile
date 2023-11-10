.PHONY: all

all: Makefile.coq
	$(MAKE) -f Makefile.coq all

Makefile.coq:
	coq_makefile -f _CoqProject -o Makefile.coq

%:: Makefile.coq
	$(MAKE) -f Makefile.coq $@
