OPAM=opam
EXEC=${OPAM} config exec
DUNE=${EXEC} jbuilder --

.PHONY: all build clean test top

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
	${DUNE} exec -- redtt load-file natural.red
	${DUNE} exec -- redtt load-file integer.red
	${DUNE} exec -- redtt load-file test.red
	${DUNE} exec -- redtt load-file invariance.red
	${DUNE} exec -- redtt load-file univalence.red

test:
	@${DUNE} build @runtest

top:
	@${DUNE} utop src/lib
