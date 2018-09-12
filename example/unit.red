import ntype

data unit where
| triv

let unit/prop : is-prop unit =
  λ [ triv → λ [ triv → λ _ → triv ] ]

let unit/contr : is-contr unit =
  ( triv , λ a → unit/prop a triv )
