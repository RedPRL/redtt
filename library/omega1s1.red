import path
import hlevel
import J
import int
import s1
import retract
import pi
import hlevel-contr
import equivalence

def s1-univ-cover : s1 → type =
  elim [
  | base → int
  | loop i → ua _ _ isuc/equiv i
  ]

def Ω1s1 : type = path s1 base base

def loopn : int → Ω1s1 =
  elim [
  | pos n →
    elim n [
    | zero → refl
    | suc (n → loopn) →
      -- this is trans, but let's expand the definition
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

def encode (x : s1) (p : path s1 base x) : s1-univ-cover x =
  coe 0 1 (pos zero) in λ i → s1-univ-cover (p i)

def winding (l : path s1 base base) : int = encode base l

def winding-loopn : (n : int) → path int (winding (loopn n)) n =
  elim [
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

/-

def decode-square (n : int)
  : [i j] s1 [
    | i=0 → loopn n j
    | i=1 → loopn (isuc n) j
    | j=0 → base
    | j=1 → loop i
    ]
  =
  elim n [
  | pos n → λ i j → comp 0 i (loopn (pos n) j) [ j=0 → refl | j=1 i → loop i ]
  | negsuc n →
    elim n [
    | zero → λ i j → comp 1 i base [ j=0 → refl | j=1 i → loop i ]
    | suc n → λ i j → comp 1 i (loopn (negsuc n) j) [ j=0 → refl | j=1 i → loop i ]
    ]
  ]

def decode (x : s1) : s1-univ-cover x → path s1 base x =
  elim x [
  | base → loopn
  | loop i → λ y j → let n : int = coe i 0 y in λ k → s1-univ-cover (loop k) in
    comp 0 i (decode-square n i j) [
    | ∂[j] → refl
    | i=1 k → loopn (isuc-pred y k) j
    ]
  ]

-/

-- the following symmetric version uses vproj instead of coe in V (thanks to Evan).

def decode-square
  : (n : int)
  → [i j] s1 [
    | i=0 → loopn (pred n) j
    | i=1 → loopn n j
    | j=0 → base
    | j=1 → loop i
    ]
  =
  elim [
  | pos n →
    elim n [
    | zero → λ i j → comp 1 i base [ j=0 → refl | j=1 i → loop i ]
    | suc n → λ i j → comp 0 i (loopn (pos n) j) [ j=0 → refl | j=1 i → loop i ]
    ]
  | negsuc n → λ i j → comp 1 i (loopn (negsuc n) j) [ j=0 → refl | j=1 i → loop i ]
  ]

def decode : (x : s1) → s1-univ-cover x → path s1 base x =
  elim [
  | base → loopn
  | loop i → λ y j →
    let n : int = ua/proj int int isuc/equiv i y in
    comp 0 1 (decode-square n i j) [
    | ∂[j] | i=1 → refl
    | i=0 k → loopn (pred-isuc y k) j
    ]
  ]

def loopn-winding (l : Ω1s1) : path _ (loopn (winding l)) l =
  J _ l (λ p → path (path s1 base (p 1)) (decode (p 1) (encode (p 1) p)) p) refl

def winding/equiv : equiv Ω1s1 int =
  iso→equiv _ _ (winding, (loopn, (winding-loopn, loopn-winding)))

def winding/path : path^1 _ Ω1s1 int =
  ua Ω1s1 int winding/equiv

opaque
def Ω1s1/set : has-hlevel set Ω1s1 =
  retract/hlevel set Ω1s1 int (winding, loopn, loopn-winding) int/set

opaque
def s1/groupoid : is-groupoid s1 =
  let from-base : (s : s1) → is-set (path s1 base s) =
    elim [
    | base → Ω1s1/set
    | loop i →
      prop→prop-over (λ j → is-set (path s1 base (loop j)))
        (has-hlevel/prop set Ω1s1)
        Ω1s1/set Ω1s1/set i
    ]
  in
  elim [
  | base → from-base
  | loop i →
    prop→prop-over (λ j → (s : s1) → is-set (path s1 (loop j) s))
      (pi/hlevel prop s1 (λ s → is-set (path s1 base s))
        (λ s → has-hlevel/prop set (path s1 base s)))
      from-base from-base i
  ]
