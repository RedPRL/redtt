import s1
import equivalence
import univalence

data s2 where
| base
| surf @ i j [
  | i=0 → base
  | i=1 → base
  | j=0 → base
  | j=1 → base
  ]

let hopf (a : s2) : type =
  elim a [
  | base → s1
  | surf i j →
    comp 0 1 (rotate/path (loop j) i) [
    | i=0 → refl
    | i=1 → refl
    | j=0 → λ k → UA/IdEquiv s1 k i
    | j=1 → λ k → UA/IdEquiv s1 k i
    ]
  ]
