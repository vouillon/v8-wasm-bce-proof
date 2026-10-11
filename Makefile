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

# What the model cites from the C++ code: make anchors V8_DIR=<v8 dir>
anchors:
	python3 check-model-anchors.py $(V8_DIR)

# All the checks (check.sh): make check V8_DIR=<v8 dir> [V8_COMMIT=<commit>]
check:
	./check.sh $(V8_DIR) $(V8_COMMIT)

.PHONY: all clean assumptions anchors check
