OPAM=opam
EXEC=${OPAM} config exec
DUNE=${EXEC} jbuilder --

.PHONY: all build clean test top

all: build

build:
	@${DUNE} build @install

clean:
	@${DUNE} clean

test:
	@${DUNE} build @runtest

doc:
	@${DUNE} build @doc

top:
	@${DUNE} utop src/lib
