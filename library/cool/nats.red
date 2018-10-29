import prelude
import data.nat
import basics.isotoequiv

/-
data nat where
| zero
| suc (x : nat)
-/

data binnat where
| nil
| cons1 (x : binnat)
| cons2 (x : binnat)

def double/nat : nat → nat =
  elim [
  | zero → zero
  | suc (_ → ih) → suc (suc ih)
  ]

def binnat→nat : binnat → nat =
  elim [
  | nil → zero
  | cons1 (_ → ih) → suc (double/nat ih)
  | cons2 (_ → ih) → suc (suc (double/nat ih))
  ]

def suc/binnat : binnat → binnat =
  elim [
  | nil → cons1 nil
  | cons1 n → cons2 n
  | cons2 (_ → ih) → cons1 ih
  ]

def nat→binnat : nat → binnat =
  elim [
  | zero → nil
  | suc (_ → ih) → suc/binnat ih
  ]

def binnat→nat/suc (n : binnat)
  : path _ (binnat→nat (suc/binnat n)) (suc (binnat→nat n)) =
  elim n [
  | nil → refl
  | cons1 _ → refl
  | cons2 (_ → ih) → λ i → suc (double/nat (ih i))
  ]

def nat→binnat→nat (n : nat)
  : path _ (binnat→nat (nat→binnat n)) n =
  elim n [
  | zero → refl
  | suc (n → ih) → trans nat (binnat→nat/suc (nat→binnat n)) (λ i → suc (ih i))
  ]

/-
-- ?-
def nat≃binnat : equiv nat binnat =
  iso→equiv _ _
    (nat→binnat,
     binnat→nat,
     elim [
     | nil → refl
     | cons0 (n → ih) → λ i → ?
     | cons1 _ → ?_
     ]
     ,
     ?_)
-/
