import ntype

data unit where
| triv

let unit/prop : IsProp unit =
  λ a →
  elim a [
  | triv → λ b →
    elim b [ triv → λ _ → triv ]
  ]

let unit/contr : IsContr unit =
  ( triv , λ a → unit/prop a triv )
