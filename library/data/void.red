import prelude

data void where

def neg (A : type) : type =
  A → void

def void/prop : is-prop void =
  elim []

def neg/prop (A : type) : is-prop (neg A) = 
  λ u v → funext A (λ _ → void) u v (λ n → elim (u n) [])