OPAM=opam
EXEC=${OPAM} config exec
DUNE=${EXEC} dune --

.PHONY: all build clean doc help examples install reinstall top

all: build

build:
	@${DUNE} build @install

clean:
	@${DUNE} clean

doc:
	@${DUNE} build @doc

help:
	@${DUNE} exec -- redtt help

examples:
	$(MAKE) -C example all

install:
	${OPAM} install redtt

reinstall:
	${OPAM} reinstall redtt

top:
	@${DUNE} utop src/core
