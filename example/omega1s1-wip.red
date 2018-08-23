import path
import int
import s1

let UA (A,B : type) (E : Equiv A B) : Path^1 type A B =
  λ i →
    `(V i A B E)

let s1-univ-cover (x : s1) : type =
  elim x [
  | base ⇒ int
  | loop i ⇒ UA _ _ isuc-equiv i
  ]

let loopn (n : int) : Path s1 base base =
  elim n [
  | pos n ⇒
    elim n [
    | zero ⇒ refl
    | suc (n ⇒ loopn) ⇒ trans s1 loopn (λ i → loop i)
    ]
  | negsuc n ⇒
    elim n [
    | zero ⇒ symm s1 (λ i → loop i)
    | suc (n ⇒ loopn) ⇒ trans s1 loopn (symm s1 (λ i → loop i))
    ]
  ]

let winding (l : Path s1 base base) : int =
  coe 0 1 (pos zero) in λ i → s1-univ-cover (l i)

let winding-loopn (n : int) : Path int (winding (loopn n)) n =
  elim n [
  | pos n ⇒
    elim n [
    | zero ⇒ refl
    | suc (n ⇒ loopn) ⇒ λ i → isuc (loopn i)
    ]
  | negsuc n ⇒
    elim n [
    | zero ⇒ refl
    | suc (n ⇒ loopn) ⇒ λ i → pred (loopn i)
    ]
  ]
