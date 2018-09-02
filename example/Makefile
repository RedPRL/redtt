OPAM=opam
EXEC=${OPAM} config exec
DUNE=${EXEC} dune --

RED_FILES=$(wildcard *.red)

all:
	for f in ${RED_FILES}; do ${DUNE} exec -- redtt load-file $${f}; done
