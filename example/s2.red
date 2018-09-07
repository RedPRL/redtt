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
    comp 0 1 s1 [
    | j=0 → UA s1 s1 (IdEquiv s1)
    | j=1 → UA s1 s1 (IdEquiv s1)
    | i=0 → UA s1 s1 (IdEquiv s1)
    | i=1 → rotate/path (loop j)
    ]
  ]
