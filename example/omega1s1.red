import path
import J
import int
import s1

let UA (A B : type) (E : Equiv A B) : Path^1 type A B =
  λ i →
    `(V i A B E)

let UAproj (A B : type) (E : Equiv A B) (i : dim) (x : UA A B E i) : B =
  `(vproj i x (fst E))

let s1-univ-cover (x : s1) : type =
  elim x [
  | base → int
  | loop i → UA _ _ isuc-equiv i
  ]

let Ω1s1 : type = Path s1 base base

let loopn (n : int) : Ω1s1 =
  elim n [
  | pos n →
    elim n [
    | zero → refl
    | suc (n → loopn) →
      ; this is trans, but let's expand the definition
      λ i → comp 0 1 (loopn i) [ i=0 → refl | i=1 j → loop j ]
    ]
  | negsuc n →
    elim n [
    | zero →
      λ i → comp 1 0 base [ i=0 → refl | i=1 j → loop j ]
    | suc (n → loopn) →
      λ i → comp 1 0 (loopn i) [ i=0 → refl | i=1 j → loop j ]
    ]
  ]

let encode (x : s1) (p : Path s1 base x) : s1-univ-cover x =
  coe 0 1 (pos zero) in λ i → s1-univ-cover (p i)

let winding (l : Path s1 base base) : int = encode base l

let winding-loopn (n : int) : Path int (winding (loopn n)) n =
  elim n [
  | pos n →
    elim n [
    | zero → refl
    | suc (n → loopn) → λ i → isuc (loopn i)
    ]
  | negsuc n →
    elim n [
    | zero → refl
    | suc (n → loopn) → λ i → pred (loopn i)
    ]
  ]

;let decode-square (n : int)
;  : [i j] s1 [
;    | i=0 → loopn n j
;    | i=1 → loopn (isuc n) j
;    | j=0 → base
;    | j=1 → loop i
;    ]
;  =
;  elim n [
;  | pos n → λ i j → comp 0 i (loopn (pos n) j) [ j=0 → refl | j=1 i → loop i ]
;  | negsuc n →
;    elim n [
;    | zero → λ i j → comp 1 i base [ j=0 → refl | j=1 i → loop i ]
;    | suc n → λ i j → comp 1 i (loopn (negsuc n) j) [ j=0 → refl | j=1 i → loop i ]
;    ]
;  ]
;
;let decode (x : s1) : s1-univ-cover x → Path s1 base x =
;  elim x [
;  | base → loopn
;  | loop i → λ y j → let n : int = coe i 0 y in λ k → s1-univ-cover (loop k) in
;    comp 0 i (decode-square n i j) [
;    | ∂[j] → refl
;    | i=1 k → loopn (isuc-pred y k) j
;    ]
;  ]

; the following symmetric version uses vproj instead of coe in V (thanks to Evan).

let decode-square (n : int)
  : [i j] s1 [
    | i=0 → loopn (pred n) j
    | i=1 → loopn n j
    | j=0 → base
    | j=1 → loop i
    ]
  =
  elim n [
  | pos n →
    elim n [
    | zero → λ i j → comp 1 i base [ j=0 → refl | j=1 i → loop i ]
    | suc n → λ i j → comp 0 i (loopn (pos n) j) [ j=0 → refl | j=1 i → loop i ]
    ]
  | negsuc n → λ i j → comp 1 i (loopn (negsuc n) j) [ j=0 → refl | j=1 i → loop i ]
  ]

let decode (x : s1) : s1-univ-cover x → Path s1 base x =
  elim x [
  | base → loopn
  | loop i → λ y j →
    let n : int =
      UAproj int int isuc-equiv i y
    in
    comp 0 1 (decode-square n i j) [
    | ∂[j] | i=1 → refl
    | i=0 k → loopn (pred-isuc y k) j
    ]
  ]

let loopn-winding (l : Ω1s1) : Path _ (loopn (winding l)) l =
  J s1 base (λ x p → Path (Path s1 base x) (decode x (encode x p)) p) refl base l

let winding/equiv : Equiv Ω1s1 int =
  Iso/Equiv _ _ (winding, (loopn, (winding-loopn, loopn-winding)))

let winding/path : Path^1 _ Ω1s1 int =
  UA Ω1s1 int winding/equiv
