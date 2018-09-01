import path
import J
import int
import s1

let UA (A,B : type) (E : Equiv A B) : Path^1 type A B =
  λ i →
    `(V i A B E)

let UAproj (A,B : type) (E : Equiv A B) (i : dim) (x : UA A B E i) : B = `(vproj i x A B E)

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

;let decode-square (n : int)
;  : [i j] s1 [
;    | i=0 ⇒ loopn n j
;    | i=1 ⇒ loopn (isuc n) j
;    | j=0 ⇒ base
;    | j=1 ⇒ loop i
;    ]
;  =
;  elim n [
;  | pos n ⇒ λ i j → comp 0 i (loopn (pos n) j) [ j=0 ⇒ refl | j=1 ⇒ λ i → loop i ]
;  | negsuc n ⇒
;    elim n [
;    | zero ⇒ λ i j → comp 1 i base [ j=0 ⇒ refl | j=1 ⇒ λ i → loop i ]
;    | suc n ⇒ λ i j → comp 1 i (loopn (negsuc n) j) [ j=0 ⇒ refl | j=1 ⇒ λ i → loop i ]
;    ]
;  ]
;
;let decode (x : s1) : (s1-univ-cover x) → Path s1 base x =
;  elim x [
;  | base ⇒ loopn
;  | loop i ⇒ λ y j → let n : int = coe i 0 y in λ k → s1-univ-cover (loop k) in
;    comp 0 i (decode-square n i j) [
;    | j=0 ⇒ refl
;    | j=1 ⇒ refl
;    | i=1 ⇒ λ k → loopn (isuc-pred y k) j
;    ]
;  ]

; the following symmetric version uses vproj instead of coe in V (thanks to Evan).

let decode-square (n : int)
  : [i j] s1 [
    | i=0 ⇒ loopn (pred n) j
    | i=1 ⇒ loopn n j
    | j=0 ⇒ base
    | j=1 ⇒ loop i
    ]
  =
  elim n [
  | pos n ⇒
    elim n [
    | zero ⇒ λ i j → comp 1 i base [ j=0 ⇒ refl | j=1 ⇒ λ i → loop i ]
    | suc n ⇒ λ i j → comp 0 i (loopn (pos n) j) [ j=0 ⇒ refl | j=1 ⇒ λ i → loop i ]
    ]
  | negsuc n ⇒ λ i j → comp 1 i (loopn (negsuc n) j) [ j=0 ⇒ refl | j=1 ⇒ λ i → loop i ]
  ]

let decode (x : s1) : (s1-univ-cover x) → Path s1 base x =
  elim x [
  | base ⇒ loopn
  | loop i ⇒ λ y j →
    let n : int =
      UAproj int int isuc-equiv i y
    in
    comp 0 1 (decode-square n i j) [
    | j=0 ⇒ refl
    | j=1 ⇒ refl
    | i=0 ⇒ λ k → loopn (pred-isuc y k) j
    | i=1 ⇒ refl
    ]
  ]

let loopn-winding (l : Path s1 base base) : Path (Path s1 base base) (loopn (winding l)) l =
  J s1 base (λ x p → Path (Path s1 base x) (decode x (encode x p)) p) refl base l

let winding-equiv : Equiv (Path s1 base base) int =
  Iso/Equiv _ _ <winding, <loopn, <winding-loopn, loopn-winding>>>
