OPAM=opam
EXEC=${OPAM} config exec
DUNE=${EXEC} dune --

all:
	${DUNE} exec -- redtt load-file nat.red
	${DUNE} exec -- redtt load-file int.red
	${DUNE} exec -- redtt load-file bool.red
	${DUNE} exec -- redtt load-file omega1s1-wip.red
	${DUNE} exec -- redtt load-file torus.red
	${DUNE} exec -- redtt load-file modal.red
	${DUNE} exec -- redtt load-file isotoequiv.red
	${DUNE} exec -- redtt load-file invariance.red
	${DUNE} exec -- redtt load-file univalence.red
