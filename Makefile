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

top:
	@${DUNE} utop src/lib
