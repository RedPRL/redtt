OPAM=opam
EXEC=${OPAM} exec
DUNE=${EXEC} dune --

RED_FILES=$(wildcard ./**/*.red)

all:
	for f in ${RED_FILES}; do ${DUNE} exec -- redtt load-file $${f} || exit -1 ; done
