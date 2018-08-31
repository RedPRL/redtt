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
    | suc (n ⇒ loopn) ⇒
      ; this is trans, but let's expand the definition
      λ i → comp 0 1 (loopn i) [ i=0 ⇒ refl | i=1 ⇒ λ j → loop j ]
    ]
  | negsuc n ⇒
    elim n [
    | zero ⇒
      λ i → comp 1 0 base [ i=0 ⇒ refl | i=1 ⇒ λ j → loop j ]
    | suc (n ⇒ loopn) ⇒
      λ i → comp 1 0 (loopn i) [ i=0 ⇒ refl | i=1 ⇒ λ j → loop j ]
    ]
  ]

let encode (x : s1) (p : Path s1 base x) : s1-univ-cover x =
  coe 0 1 (pos zero) in λ i → s1-univ-cover (p i)

let winding (l : Path s1 base base) : int = encode base l

;let winding-loopn (n : int) : Path int (winding (loopn n)) n =
;  elim n [
;  | pos n ⇒
;    elim n [
;    | zero ⇒ refl
;    | suc (n ⇒ loopn) ⇒ λ i → isuc (loopn i)
;    ]
;  | negsuc n ⇒
;    elim n [
;    | zero ⇒ refl
;    | suc (n ⇒ loopn) ⇒ λ i → pred (loopn i)
;    ]
;  ]

let decode-square (n : int)
  : [i j] s1 [
    | i=0 ⇒ loopn n j
    | i=1 ⇒ loopn (isuc n) j
    | j=0 ⇒ base
    | j=1 ⇒ loop i
    ]
  =
  λ i j →
    elim n [
    | pos n ⇒
      comp 0 i (loopn (pos n) j) [ j=0 ⇒ refl | j=1 ⇒ λ i → loop i ]
    | negsuc n ⇒
      elim n [
      | zero ⇒ comp 1 i base [ j=0 ⇒ refl | j=1 ⇒ λ i → loop i ]
      | suc n ⇒ comp 1 i (loopn (negsuc n) j) [ j=0 ⇒ refl | j=1 ⇒ λ i → loop i ]
      ]
    ]

;let decode (x : s1) (y : s1-univ-cover x) : Path s1 base x =
;  elim x [
;  | base ⇒ loopn y
;  | loop i ⇒ λ n j → ?
;  ]

; let loopn-winding (x : s1) (l : Path s1 base x) : Path (Path s1 base base) (loopn (winding', l)) l =
;   J

; let J
;  (A : type) (a : A)
;  (C : (x : A) (p : Path _ a x) → type) (d : C a (λ _ → a))
;  (x : A) (p : Path _ a x)
