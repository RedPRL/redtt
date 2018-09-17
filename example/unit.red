import ntype

data unit where
| triv

let unit/prop : is-prop unit =
  λ * * → refl

let unit/contr : is-contr unit =
  ( triv , λ a → unit/prop a triv )
