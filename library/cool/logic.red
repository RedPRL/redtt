import prelude
import data.void
import data.bool
import paths.bool
import basics.hedberg

import basics.retract
import data.susp
import data.unit
import data.truncation
import paths.hlevel

def no-double-neg-elim (f : (A : type) → stable A) : void =
  let f2 = f bool in

  -- transport along the path induced from `not` by univalence
  let tf2 = coe 0 1 f2 in λ i → stable (not/path i) in

  -- transporting a dependent function produces a path to the original
  let apdf : path _ tf2 f2 = λ i → coe i 1 (f (not/path i)) in λ j → stable (not/path j) in

  -- tf2 is equal to a composition of transporting the argument backwards along `neg (neg (symm not/path))`...
  let inner (u : neg (neg bool)) : neg (neg bool) = coe 0 1 u in λ i → neg (neg (symm^1 type not/path i)) in

  -- ... and then `f2` applied to result forwards along `not/path`
  -- however transporting along an univalence-induced path equals applying the original iso
  -- thus `tf2 u = not (f2 (inner u))`

  -- `neg A` is a prop, so there is a path
  let u→inner (u : neg (neg bool)) : path _ u (inner u) = neg/prop (neg bool) u (inner u) in

  -- lift it to a path into `tf2`
  let notf2→tf2 (u : neg (neg bool)) : path _ (not (f2 u)) (tf2 u) = λ i → not (f2 (u→inner u i)) in

  -- and compose with `apdf` to obtain a contradictory path
  let contra (u : neg (neg bool)) : path _ (not (f2 u)) (f2 u) = trans _ (notf2→tf2 u) (λ i → apdf i u) in

  let nnb : neg (neg bool) = λ negb → negb tt in
  not/neg (f2 nnb) (contra nnb)

def no-excluded-middle (g : (A : type) → dec A) : void =
  no-double-neg-elim (λ A → dec→stable A (g A))

-- 7.2.2
def hrel/set-equiv 
  (A : type) (R : A → A → type) 
  (R/prop : (x y : A) → is-prop (R x y))
  (R/refl : (x : A) → R x x) 
  (R/id : (x y : A) → R x y → path A x y) 
  : (is-set A) × ((x y : A) → equiv (R x y) (path A x y))
  = 
  let eq = path-retract/equiv A R (λ a b → 
    ( R/id a b
    , λ p → coe 0 1 (R/refl a) in λ j → R a (p j)
    , λ rab → R/prop a b (coe 0 1 (R/refl a) in λ j → R a (R/id a b rab j)) rab
    )) in
  ( λ x y → coe 0 1 (R/prop x y) in λ j → is-prop (ua _ _ (eq x y) j)
  , eq 
  )

-- Hedberg's theorem is a corollary
def paths-stable→set/alt (A : type) (st : (x y : A) → stable (path A x y)) : is-set A =
  (hrel/set-equiv A (λ x y → neg (neg (path A x y)))
    (λ x y → neg/prop (neg (path A x y)))
    (λ _ np → np refl)
    st
  ).fst

def P (A : type) (A/prop : is-prop A) (s1 s2 : susp A) : type = 
  let Au (a : A) = ua A unit (prop/unit A A/prop a) in
  let uA (a : A) = symm^1 _ (Au a) in
  let Nty : susp A → type = elim [north → unit | south → A | merid c n → uA c n] in
  let Sty : susp A → type = elim [north → A | south → unit | merid c n → Au c n] in
    elim s1 [
    | north → Nty s2
    | south → Sty s2
    | merid a i → 
      elim s2 in λ s → path^1 _ (Nty s) (Sty s) [ 
      | north → uA a
      | south → Au a
      | merid b j → λ m → 
        comp 0 1 (connection/both^1 type (uA a) (Au a) m j) [
        | m=0 k → uA (A/prop a b k) j
        | m=1 k → Au (A/prop a b k) j
        | ∂[j] → refl
        ]
      ] i
    ]

def P/refl (A : type) (A/prop : is-prop A) (x : susp A) : P A A/prop x x = 
  let Au (a : A) = ua A unit (prop/unit A A/prop a) in
  let uA (a : A) = symm^1 _ (Au a) in

  let pface (B : type) (p : 𝕀 → B) (j i : 𝕀) : B =
    comp 1 j (p i) [
    | i=0 → refl
    | i=1 → p
    ] in

  let pface/ua (a : A) : (i : 𝕀) → pface^1 type (uA a) 0 i 
    = λ i → 
      comp 1 0 (coe 1 i a in uA a) in
      λ j → pface^1 _ (uA a) j i [
      | i=0 → refl
      | i=1 k → coe 1 k a in uA a
      ] in

  let qface/ua (a : A) : (i : 𝕀) → trans/filler^1 _ (uA a) (Au a) 1 i 
    = λ i → 
      comp 0 1 (coe 1 i a in uA a) in
      λ j → trans/filler^1 _ (uA a) (Au a) j i [  
      | i=0 → refl
      | i=1 → λ k → coe 0 k a in Au a
      ] in
  
  let pq/filler (B : type) (p : 𝕀 → B) (q : [i] B [i=0 → p 1]) (j i : 𝕀) : B =
    comp 0 j (p 0) [
       | i=0 → pface        B p   0
       | i=1 → trans/filler B p q 1
    ] in
  
  let pq (a : A) : (i : 𝕀) → pq/filler^1 type (uA a) (Au a) 1 i
    = λ i → 
    comp 0 1 (coe 1 0 a in uA a) in 
    λ j → pq/filler^1 _ (uA a) (Au a) j i [ 
    | i=0 → pface/ua a
    | i=1 → qface/ua a
    ] in
  
  let pqu/filler (B : type) (p : 𝕀 → B) (q : [i] B [i=0 → p 1]) (j i : 𝕀) : B =
    comp 0 1 (pq/filler B p q j i) [
      | i=0 → refl
      | i=1 → refl
    ] in
  
  let pqu (a : A) : (i : 𝕀) → pqu/filler^1 type (uA a) (Au a) 1 i
    = λ i → 
      comp 0 1 (box refl [coe 1 0 a in uA a | coe 1 0 a in uA a]) in 
      λ j → pqu/filler^1 _ (uA a) (Au a) j i [ 
      | i=0 → pface/ua a
      | i=1 → qface/ua a
      ] in

  elim x [
    | north → ★
    | south → ★
    | merid a i → pqu a i
    ]

/-
def P/prop (A : type) (A/prop : is-prop A) (x y : susp A) : is-prop (P A A/prop x y) = 
  λ c d i → ?wat

def P/id (A : type) (A/prop : is-prop A) (x y : susp A) (Pxy : P A A/prop x y) : path (susp A) x y = ?wat

-- 10.1.13
def suspension-lemma (A : type) (A/prop : is-prop A) : 
  (is-set (susp A)) × (equiv A (path (susp A) north south)) = 
  let Au (a : A) = ua A unit (prop/unit A A/prop a) in
  let uA (a : A) = symm^1 _ (Au a) in
  let P (s1 s2 : susp A) : type = 
    elim s1 [
    | north → 
      elim s2 [
      | north → unit
      | south → A
      | merid b j → uA b j
      ]
    | south → 
      elim s2 [
      | north → A
      | south → unit
      | merid b j → Au b j
      ]
    | merid a i → 
      let mot (s : susp A) : type^1 =
        path^1 
          type 
          (elim s [north → unit | south → A | merid c n → uA c n]) 
          (elim s [north → A | south → unit | merid c n → Au c n])
      in 
      elim s2 in mot [ 
      | north → uA a
      | south → Au a
      | merid b j → λ i → 
        comp 0 1 (connection/both^1 type (uA a) (Au a) i j) [
        | i=0 k → uA (A/prop a b k) j
        | i=1 k → Au (A/prop a b k) j
        | ∂[j] → refl
        ]
      ] i
    ] in
  ?suspension-hole

def is-surjective (A B : type) (f : A → B) : type = (b : B) → trunc (fiber A B f b)

def is-embedding (A B : type) (f : A → B) : type = (x y : A) → equiv (path A x y) (path B (f x) (f y))

def is-injective (A B : type) (A/set : is-set A) (B/set : is-set B) (f : A → B) : type = (x y : A) → path B (f x) (f y) → path A x y

def injective→embedding (A B : type) (A/set : is-set A) (B/set : is-set B) (f : A → B) : injective A B A/set B/set f → embedding A B f = 
  λ f/inj x y → 
    prop/equiv (path A x y) (path B (f x) (f y)) 
               (A/set x y) (B/set (f x) (f y)) 
               (λ p i → f (p i)) (f/inj x y)

def has-choice (X : type) (Y : X → type) : type = (X/set : is-set X) → (Y/set : (x : X) → is-set (Y x)) → ((x : X) → trunc (Y x)) → trunc ((x : X) → Y x)

def LEM (A : type) : type = (A/prop : is-prop A) → dec A

def choice→LEM (choice-ax : (X : type) → (Y : X → type) → has-choice X Y) : (A : type) → LEM A = 
  λ A A/prop →
  let f (b : bool) : susp A = elim b [ 
   | tt → south
   | ff → north
   ] in
  ?choice-hole
-/