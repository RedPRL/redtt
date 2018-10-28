import prelude

data unit where
| ★

def unit/prop : is-prop unit =
  λ * * → refl

def unit/contr : is-contr unit =
  ( ★ , λ a → unit/prop a ★ )
