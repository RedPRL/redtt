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
| cons0 (x : binnat)
| cons1 (x : binnat)

def double/nat : nat → nat =
  elim [
  | zero → zero
  | suc (_ → ih) → suc (suc ih)
  ]

def binnat→nat : binnat → nat =
  elim [
  | nil → zero
  | cons0 (_ → ih) → double/nat ih
  | cons1 (_ → ih) → suc (double/nat ih)
  ]

def suc/binnat : binnat → binnat =
  elim [
  | nil → cons1 nil
  | cons0 n → cons1 n
  | cons1 (_ → ih) → cons0 ih
  ]

def nat→binnat : nat → binnat =
  elim [
  | zero → nil
  | suc (_ → ih) → suc/binnat ih
  ]

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
