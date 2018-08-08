import path
import int

let UA (A,B : type) (E : Equiv A B) : Path^1 type A B =
  λ i →
    `(V i A B E)

data s1 where
| s1/base
| s1/loop @ i [i=0 ⇒ s1/base | i=1 ⇒ s1/base]

let s1-univ-cover (x : s1) : type =
  elim x [
  | s1/base ⇒ int
  | s1/loop i ⇒ UA _ _ isuc-equiv i
  ]

let loopn (n : int) : Path s1 s1/base s1/base =
  elim n [
  | pos n ⇒
    elim n [
    | zero ⇒ λ _ → s1/base
    | suc (n ⇒ loopn) ⇒ trans s1 (λ i → s1/loop i) loopn
    ]
  | negsuc n ⇒
    elim n [
    | zero ⇒ symm s1 (λ i → s1/loop i)
    | suc (n ⇒ loopn) ⇒ trans s1 (symm s1 (λ i → s1/loop i)) loopn
    ]
  ]

let winding (l : Path s1 s1/base s1/base) : int =
  coe 0 1 (pos zero) in λ i → s1-univ-cover (l i)

let two : int = pos (suc (suc zero))

let winding-loop-testing0 : Path int two (winding (loopn two)) =
  λ _ → two

let five : int = pos (suc (suc (suc (suc zero))))

let winding-loop-testing1 : Path int five (winding (loopn five)) =
  λ _ → five

