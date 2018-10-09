OPAM=opam
EXEC=${OPAM} config exec
DUNE=${EXEC} dune --

.PHONY: all build clean doc help library install reinstall top

all: build

build:
	@${DUNE} build @install

clean:
	@${DUNE} clean

doc:
	@${DUNE} build @doc

help:
	@${DUNE} exec -- redtt help

library:
	$(MAKE) -C library all

install:
	${OPAM} install redtt

reinstall:
	${OPAM} reinstall redtt

top:
	@${DUNE} utop src/core
