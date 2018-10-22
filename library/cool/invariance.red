import prelude
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
def nat→list/path : path^1 type nat (list unit) = ua _ _ nat→list/equiv

-- We can transport functions between these two implementations, and run them!
--   from nat → nat to list unit → list unit...

def double/nat : nat → nat =
  elim [
  | zero → zero
  | suc (_ → ih) → suc (suc ih)
  ]

def double/list : list unit → list unit =
  coe 0 1 double/nat in λ i → nat→list/path i → nat→list/path i

def double/list/one : list unit = double/list (cons triv nil)
meta ⦉ print normalize double/list/one ⦊

--   from list unit → list unit to nat → nat...

def pred : nat → nat =
  coe 1 0 (tail unit) in λ i → nat→list/path i → nat→list/path i

def pred/two : nat = pred (suc (suc zero))
meta ⦉ print normalize pred/two ⦊

--    from list (list unit) → nat to list nat → list unit...

def mystery (f : list (list unit) → nat) : list nat → list unit =
  coe 0 1 f in λ i → list (symm^1 type nat→list/path i) → nat→list/path i

-- These two implementations of natural numbers are equal!

def nat-impl : type^1 = (A : type) × A × (A → A)
def nat-impl/nat : nat-impl = (nat, zero, λ n → suc n)
def nat-impl/list : nat-impl = (list unit, nil, λ xs → cons triv xs)

def nat-impl/equal : path^1 nat-impl nat-impl/nat nat-impl/list =
  λ i →
  (nat→list/path i,
   coe 0 i zero in nat→list/path,
   -- MORTAL
   λ v → let v' : nat→list/path i = (suc v, cons triv (v .vproj)) in v'
  )

-- We can also transport proofs *about* these implementations.
-- pred was defined as the coercion of tail, so...

def tail-cons (xs : list unit) : path (list unit) (tail unit (cons triv xs)) xs = refl

def pred-suc : (n : nat) → path nat (pred (suc n)) n =
  let pred-tail
    : pathd (λ i → nat→list/path i → nat→list/path i) pred (tail unit)
    = λ i → coe 1 i (tail unit) in λ i → nat→list/path i → nat→list/path i in
  let suc-cons
    : pathd (λ i → nat→list/path i → nat→list/path i) (λ n → suc n) (λ xs → cons triv xs)
    = λ i → (nat-impl/equal i) .snd .snd in
  coe 1 0 tail-cons in
    λ i → (x : nat→list/path i) → path (nat→list/path i) (pred-tail i (suc-cons i x)) x
  -- (x : nat)  → path nat  (pred (suc  x)) x
  -- (x : list) → path list (tail (cons x)) x

/- MORTAL bugs

def mystery/concat : list unit =
  let sum (ls : list (list unit)) : nat = length unit (concatenate unit ls) in
  let ls : list nat = cons (suc zero) (cons zero nil) in -- [1,0]
  mystery sum ls
meta ⦉ print normalize mystery/concat ⦊

def mystery' (f : list nat → list unit) : list (list unit) → nat =
  coe 0 1 f in λ i → list (nat→list/path i) → (symm^1 type nat→list/path i)

def mystery'/concat : nat =
  let flatten : list nat → list unit =
    elim [
    | nil → nil
    | cons x (_ → ih) → append unit (nat→list x) ih
    ]
  in
  let ls : list (list unit) = cons (cons triv nil) (cons nil nil) in -- [[*],[]]
  mystery' flatten ls
meta ⦉ print normalize mystery'/concat ⦊

def weird (A : type) (f : list nat → A) : list (list unit) → A =
  coe 0 1 f in λ i → list (nat→list/path i) → A

def weird/sum : nat =
  let sum : list nat → nat = elim [nil → zero | cons x (_ → ih) → plus x ih] in
  let ls : list (list unit) = cons (cons triv nil) (cons (cons triv nil) nil) in
  weird nat sum ls --[[*],[*]]
-/

-- Another example, ported from
-- https://github.com/RedPRL/sml-redprl/blob/master/example/invariance.prl

import data.bool

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
