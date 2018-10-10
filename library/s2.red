import s1
import equivalence
import univalence

data s2 where
| base
| surf (i j : 𝕀) [∂[i j] → base]

def hopf : s2 → type =
  elim [
  | base → s1
  | surf i j →
    comp 0 1 s1 [
    | ∂[j] | i=0 → ua s1 s1 (id-equiv s1)
    | i=1 → rotate/path (loop j)
    ]
  ]
