import s1
import equivalence
import univalence

data s2 where
| base
| surf @ i j [∂[i j] → base]

let hopf (a : s2) : s2 → type =
  λ [
  | base → s1
  | surf i j →
    comp 0 1 s1 [
    | ∂[j] | i=0 → ua s1 s1 (id-equiv s1)
    | i=1 → rotate/path (loop j)
    ]
  ]
