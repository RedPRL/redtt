import path
import int

let UA (A,B : type) (E : Equiv A B) : Path^1 type A B =
  λ i →
    `(V i A B E)


let S1-univ-cover (x : S1) : type =
  elim x [
  | base => int
  | loop i => UA _ _ isuc-equiv i
  ]

let loopn (n : int) : Path S1 base base =
  elim n [
  | pos n =>
    elim n [
    | zero => lam _ -> base
    | suc (n => loopn) => trans S1 (lam i -> loop i) loopn
    ]
  | negsuc n =>
    elim n [
    | zero => symm S1 (lam i -> loop i)
    | suc (n => loopn) => trans S1 (symm S1 (lam i -> loop i)) loopn
    ]
  ]

let winding (l : Path S1 base base) : int =
  coe 0 1 (pos zero) in lam i -> S1-univ-cover (l i)

let two : int = pos (suc (suc zero))

let winding-loop-testing0 : Path int two (winding (loopn two)) =
  lam _ -> two

let five : int = pos (suc (suc (suc (suc zero))))

let winding-loop-testing1 : Path int five (winding (loopn five)) =
  lam _ -> five
