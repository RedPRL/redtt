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
def mere-relation/set-equiv 
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
  (mere-relation/set-equiv A (λ x y → neg (neg (path A x y)))
    (λ x y → neg/prop (neg (path A x y)))
    (λ _ np → np refl)
    st
  ).fst

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

def choice (X : type) (Y : X → type) : type = (X/set : is-set X) → (Y/set : (x : X) → is-set (Y x)) → ((x : X) → trunc (Y x)) → trunc ((x : X) → Y x)

def choiceLEM (choice-ax : (X : type) → (Y : X → type) → choice X Y) : (A : type) → (A/prop : is-prop A) → dec A = 
  λ A A/prop →
  let f (b : bool) : susp A = elim b [ 
   | tt → south
   | ff → north
   ] in
  ?choice-hole
