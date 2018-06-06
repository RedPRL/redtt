let foo : `(-> bool bool)
foo => `(λ [x] x)

let Path : `(-> [A : (U 0)] [M : A] [N : A] (U 0))

Path =>
  `(λ [A] [M] [N]
    (# <i> A [i=0 M] [i=1 N]))

let funext :
  `(->
    [A : (U 0)]
    [B : (→ A (U 0))]
    [f : (→ [x : A] (B x))]
    [g : (→ [x : A] (B x))]
    [p : (→ [x : A] (Path (B x) (f x) (g x)))]
    (Path (→ [x : A] (B x)) f g))

funext =>
  `(λ [A] [B] [f] [g] [p] <i> [x] (@ (p x) i))


let taste : `(-> bool (* bool bool))
taste =>
  λ x ->
  < x, `ff >

debug
