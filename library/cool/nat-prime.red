import data.list
import prelude 
import data.nat
import data.bool
import cool.gcd

data factor where
| o 
| s (f : factor)

def nat' : type = list factor

def is-prime-from : nat → nat → nat → bool =
  elim [
    | zero → λ _ _ → tt
    | suc (n' → f) → λ n k → 
      elim (mod n k) [
        | zero → ff
        | suc _ → f n (suc k)
      ]
  ]

def le/bool : nat → nat → bool =
  elim [
  | zero → λ _ → tt
  | suc (m → f) →
    elim [
    | zero → ff
    | suc n → f n
    ]
  ]

def and : bool → bool → bool =
  elim [
    | tt → 
      elim [
        | tt → tt
        | ff → ff
      ]
    | ff → λ _ → ff
  ]

def is-prime (n : nat) = and (is-prime-from (nat-pred (nat-pred n)) n n2)
  (not (le/bool n n1))

def check' = is-prime n8

def nth-prime : nat → nat = 
  elim [
    | zero → n2
    | suc (n' → f) → 
      
  ]

meta <: print normalize check' :>

quit

def nat/equiv/nat' : equiv nat' nat = ?
