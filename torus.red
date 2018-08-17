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
  | square i j ⇒ auto
  ]

let c2t/base (c : s1) : torus =
  elim c [
  | base ⇒ pt
  | loop i ⇒ p/two i
  ]

let c2t/transpose (c : s1) : s1 → torus =
  elim c [
  | base ⇒ λ c' →
    elim c' [
    | base ⇒ pt
    | loop j ⇒ p/two j
    ]

  | loop i ⇒ λ c' →
    elim c' [
    | base ⇒ p/one i
    | loop j ⇒ square j i
    ]
  ]



let c2t (cs : s1 × s1) : torus =
  c2t/transpose (cs.0) (cs.1)

let t2c2t (t : torus) : [i] torus [i=0 ⇒ c2t (t2c t) | i=1 ⇒ t] =
  elim t [
  | pt ⇒ auto
  | p/one i ⇒ auto
  | p/two i ⇒ auto
  | square i j ⇒ auto
  ]

