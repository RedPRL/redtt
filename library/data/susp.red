import prelude
import data.bool
import data.nat
import data.s1

-- adapted from https://github.com/mortberg/cubicaltt/blob/master/examples/susp.ctt

data (A : type) ⊢ susp where
| north
| south
| merid (a : A) (i : 𝕀) [
  | i=0 → north
  | i=1 → south
  ]

def sphere : nat → type =
  elim [
  | zero → bool
  | suc (n → sphere/n) → susp sphere/n
  ]
