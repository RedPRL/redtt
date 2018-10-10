import ntype

data unit where
| triv

def unit/prop : is-prop unit =
  λ * * → refl

def unit/contr : is-contr unit =
  ( triv , λ a → unit/prop a triv )
