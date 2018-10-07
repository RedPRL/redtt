import int
import univalence

data patch where
| num
| add1 (i : dim) [∂[i] → num]

let Interp : patch → type =
  elim [
  | num → int
  | add1 i → ua _ _ isuc/equiv i
  ]

let interp (p : path patch num num) : equiv int int =
  path→equiv int int (λ i → Interp (p i))

let test : path (equiv int int) (interp (λ i → add1 i)) isuc/equiv =
  subtype/path
    (int → int)
    (is-equiv int int)
    (is-equiv/prop int int)
    (interp (λ i → add1 i))
    isuc/equiv
    refl
