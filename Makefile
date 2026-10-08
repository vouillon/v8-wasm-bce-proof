# Build with coq_makefile from _CoqProject.
all: Makefile.coq
	$(MAKE) -f Makefile.coq all

Makefile.coq: _CoqProject
	coq_makefile -f _CoqProject -o Makefile.coq

clean: Makefile.coq
	$(MAKE) -f Makefile.coq cleanall
	rm -f Makefile.coq Makefile.coq.conf

assumptions: all
	coqc -R . BCE Assumptions.v

.PHONY: all clean assumptions
