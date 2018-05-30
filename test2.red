let welp : `bool
welp => `tt

let Path : `(-> [A : (U 0)] [M : A] [N : A] (U 0))
Path => `(lam [A] [M] [N] (# <i> A [i=0 M] [i=1 N]))
debug foo
