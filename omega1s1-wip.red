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
    | zero ⇒ λ _ → base
    | suc (n ⇒ loopn) ⇒ trans s1 (λ i → loop i) loopn
    ]
  | negsuc n ⇒
    elim n [
    | zero ⇒ symm s1 (λ i → loop i)
    | suc (n ⇒ loopn) ⇒ trans s1 (symm s1 (λ i → loop i)) loopn
    ]
  ]

let winding (l : Path s1 base base) : int =
  coe 0 1 (pos zero) in λ i → s1-univ-cover (l i)

let two : int = pos (suc (suc zero))

let winding-loop-testing0 : Path int two (winding (loopn two)) =
  λ _ → two

let nat/five : nat =
  suc (suc (suc (suc (suc zero))))

let int/25 : int =
  pos (plus nat/five (plus nat/five (plus nat/five (plus nat/five nat/five))))

let winding-loop-testing1 : Path int int/25 (winding (loopn int/25)) =
  λ _ → int/25

