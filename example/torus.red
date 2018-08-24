import path
import s1
import isotoequiv

; cubicaltt version: https://github.com/mortberg/cubicaltt/blob/master/examples/torus.ctt
; cubical agda version: https://github.com/Saizan/cubical-demo/blob/hits-transp/examples/Cubical/Examples/Torus.agda

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
  | square i j ⇒ refl
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

let t2c2t (t : torus) : Path torus (c2t (t2c t)) t =
  elim t [
  | pt ⇒ refl
  | p/one i ⇒ refl
  | p/two i ⇒ refl
  | square i j ⇒ refl
  ]


let c2t2c/transpose (c0 : s1) : (c1 : s1) → Path (s1 × s1) (t2c (c2t/transpose c0 c1)) <c0, c1> =
  elim c0
  [ base ⇒ λ c1 →
    elim c1
    [ base ⇒ refl
    | loop j ⇒ refl
    ]

  | loop i ⇒ λ c1 →
    elim c1
    [ base ⇒ refl
    | loop j ⇒ refl
    ]
  ]


let c2t2c (cs : s1 × s1) : Path (s1 × s1) (t2c (c2t cs)) cs =
  c2t2c/transpose (cs.0) (cs.1)


let torus/s1s1/iso : Iso (s1 × s1) torus =
  < c2t
  , t2c
  , t2c2t
  , c2t2c
  >


let torus/s1s1/equiv : Equiv (s1 × s1) torus =
  Iso/Equiv (s1 × s1) torus torus/s1s1/iso

let torus/s1s1/path : Path^1 type (s1 × s1) torus =
  UA (s1 × s1) torus torus/s1s1/equiv
