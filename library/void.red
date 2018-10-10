import ntype

data void where

def neg (A : type) : type =
  A → void

def void/prop : is-prop void =
  elim []
