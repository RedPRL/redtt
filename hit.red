import path

data s1 where
| s1/base
| s1/loop @ i [ i=0 ⇒ s1/base | i=1 ⇒ s1/base ]

let test : Path s1 (s1/loop 0) s1/base =
  λ _ → s1/base

debug
