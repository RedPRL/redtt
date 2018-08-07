import path

data s1 where
| s1/base
| s1/loop @ i [ i=0 ⇒ s1/base | i=1 ⇒ s1/base ]

data torus where
| pt
| p/one @ i [i=0 ⇒ pt | i=1 ⇒ pt]
| p/two @ i [i=0 ⇒ pt | i=1 ⇒ pt]
| square @ i j
  [ i=0 ⇒ p/one j
  | i=1 ⇒ p/one j
  | j=0 ⇒ p/two i
  | j=1 ⇒ p/two i ]

let t2c (t : torus) : s1 × s1 =
  elim t [
  | pt ⇒ <s1/base, s1/base>
  | p/one i ⇒ <s1/loop i, s1/base >
  | p/two i ⇒ <s1/base, s1/loop i>
  | square i j ⇒ <s1/loop j, s1/loop i>
  ]

