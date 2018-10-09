import int
import univalence

data patch where
| num
| add1 (i : 𝕀) [∂[i] → num]

def Interp : patch → type =
  elim [
  | num → int
  | add1 i → ua _ _ isuc/equiv i
  ]

def int-equiv = equiv int int

def int-equiv/path (f g : int-equiv) : path _ (f.fst) (g.fst) → path _ f g =
  subtype/path (int → int) (is-equiv int int) (is-equiv/prop int int) f g

def interp (p : path patch num num) : equiv int int =
  path→equiv int int (λ i → Interp (p i))

def test : path (equiv int int) (interp (λ i → add1 i)) isuc/equiv =
  int-equiv/path (interp (λ i → add1 i)) isuc/equiv refl
