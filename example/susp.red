import nat
import bool
import s1

-- adapted from https://github.com/mortberg/cubicaltt/blob/master/examples/susp.ctt

data susp (A : type) where
| north
| south
| merid (a : A) (i : dim) [
  | i=0 → north
  | i=1 → south
 ]

def sphere : nat → type =
  elim [
  | zero → bool
  | suc (n → sphere/n) → susp sphere/n
  ]

def sphere1 : type = sphere (suc zero)

def sphere1→s1 : sphere1 → s1 =
  elim [
  | north → base
  | south → base
  | merid b i →
    elim b in λ _ → path s1 base base [
    | ff → λ j → loop j
    | tt → refl
    ] i
  ]

def s1→sphere1 : s1 → sphere1 =
  elim [
  | base → north
  | loop i →
    trans sphere1 (λ i → merid ff i) (symm sphere1 (λ i → merid tt i)) i
  ]
