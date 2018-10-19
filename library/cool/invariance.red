import prelude
import data.bool

-- This is ported from some RedPRL examples by Carlo Angiuli:
-- https://github.com/RedPRL/sml-redprl/blob/master/example/invariance.prl

def fun→pair (A : type) (f : bool → A) : A × A =
  (f tt, f ff)

def pair→fun (A : type) (p : A × A) : bool → A =
elim [tt → p.fst | ff → p.snd]

def fun→pair-is-equiv (A : type) : is-equiv^1 _ _ (fun→pair A) =
  λ p →
    ( (pair→fun A p, refl)
    , λ fib →
      coe 1 0 (λ i → (pair→fun _ (fib.snd i), λ j → weak-connection/or _ (fib.snd) i j)) in λ j →
      path
        ((f : bool → A) × path (A × A) (f tt, f ff) p)
        (shannon/path A (fib.fst) j, fib.snd)
        (pair→fun A p, refl)
    )

def fun→pair/equiv (A : type) : equiv (bool → A) (A × A) =
  (fun→pair A, fun→pair-is-equiv A)

def fun→pair/path (A : type) : path^1 type (bool → A) (A × A) =
  ua (bool → A) (A × A) (fun→pair/equiv A)

def swap-pair (A : type) (p : A × A) : A × A =
  (p.snd, p.fst)

def swap-fun (A : type) : (bool → A) → bool → A =
  coe 1 0 (swap-pair A) in λ i →
  fun→pair/path A i → fun→pair/path A i

def swap-fun/path (A : type) : (f : bool → A) → path _ (swap-fun A (swap-fun A f)) f =
  coe 1 0 (λ _ → refl) in λ i →
  let swapcoe =
    coe 1 i (swap-pair A) in λ j →
    fun→pair/path A j → fun→pair/path A j
  in
  (f : fun→pair/path A i) → path (fun→pair/path A i) (swapcoe (swapcoe f)) f

-- A cooler example?

import data.list
import data.nat
import data.unit
import paths.list
import basics.isotoequiv

def nat→list : nat → list unit =
  elim [
  | zero → nil
  | suc (_ → xs) → cons triv xs
  ]

-- do we need this outside of the iso?
def list→nat→list (xs : list unit) :
  path (list unit) (nat→list (length unit xs)) xs =
  elim xs [
  | nil → refl
  | cons * (_ → ih) → λ i → cons triv (ih i)
  ]

-- do we need this outside of the iso?
def nat→list→nat (n : nat) : path nat (length unit (nat→list n)) n =
  elim n [
  | zero → refl
  | suc (_ → ih) → λ i → suc (ih i)
  ]

def nat→list/iso : iso nat (list unit) =
  (nat→list,
   length unit,
   elim [
   | nil → refl
   | cons * (_ → ih) → λ i → cons triv (ih i)
   ],
   elim [
   | zero → refl
   | suc (_ → ih) → λ i → suc (ih i)
   ])

def nat→list/equiv : equiv^1 nat (list unit) = iso→equiv _ _ nat→list/iso

def nat-impl : type^1 = (A : type) × A × (A → A)
def nat/nat-impl : nat-impl = (nat, zero, λ n → suc n)
def list/nat-impl : nat-impl = (list unit, nil, λ xs → cons triv xs)

def bisimulation : path^1 nat-impl nat/nat-impl list/nat-impl =
  let ua/path = ua _ _ nat→list/equiv in
  λ i →
  (ua/path i,
   coe 0 i zero in ua/path,
   -- MORTAL
   λ v → let v' : ua/path i = (suc v, cons triv (v .vproj)) in v'
  )

def cool-lemma
  : (n' n : nat)
  → path (list unit) (nat→list n') (cons triv (nat→list n))
  → path nat n' (suc n)
  =
  elim [
  | zero → λ _ p → elim (list/encode unit _ _ p) []
  | suc m → λ n p →
    let α (i : 𝕀) : nat =
      comp 0 1 (length unit (tail unit (p i))) [
      | i=0 → nat→list→nat m
      | i=1 → nat→list→nat n
      ]
    in
    λ i → suc (α i)
  ]

def unit-list/set : is-set (list unit) = list/hlevel contr _ (prop→set _ unit/prop)

/-
def nat→list/is-equiv' : is-equiv^1 _ _ nat→list =
  elim [
  | nil →
    ((zero, refl),
     λ [,] →
     elim [
     | zero → λ p i →
       (zero, unit-list/set _ _ p refl i)
     | suc _ → λ p → elim (list/encode unit _ _ p) []
     ]
    )
  | cons * (xs → ih) →
    let ((n,p),_) = ih in
    ((suc n, λ i → cons triv (p i)),
     λ (n',p') i →
     let α (j : 𝕀) : list unit = comp 1 0 (p' j) [j=0 → refl | j=1 k → cons triv (p k)] in
     (cool-lemma n' n α i, ?cfhm)
    )
  ]
-/
