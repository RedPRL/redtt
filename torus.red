import path
import s1

data torus where
| pt
| p/one @ i [i=0 ⇒ pt | i=1 ⇒ pt]
| p/two @ i [i=0 ⇒ pt | i=1 ⇒ pt]
| square @ i j
  [ i=0 ⇒ p/one j
  | i=1 ⇒ p/one j
  | j=0 ⇒ p/two i
  | j=1 ⇒ p/two i
  ]

let t2c (t : torus) : s1 × s1 =
  elim t [
  | pt ⇒ <base, base>
  | p/one i ⇒ <loop i, base>
  | p/two i ⇒ <base, loop i>
  | square i j ⇒ <loop j, loop i>
  ]

