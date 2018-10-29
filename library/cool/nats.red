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
