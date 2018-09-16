import path
import s1
import isotoequiv

-- cubicaltt version: https://github.com/mortberg/cubicaltt/blob/master/examples/torus.ctt
-- cubical agda version: https://github.com/Saizan/cubical-demo/blob/hits-transp/examples/Cubical/Examples/Torus.agda

data torus where
| pt
| p/one (i : dim) [∂[i] → pt]
| p/two (i : dim) [∂[i] → pt]
| square (i j : dim)
  [ ∂[i] → p/one j
  | ∂[j] → p/two i
  ]

let t2c : torus → s1 × s1 =
  λ [
  | pt → (base, base)
  | p/one i → (loop i, base)
  | p/two i → (base, loop i)
  | square i j → (loop j, loop i)
  ]

let c2t/base : s1 → torus =
  λ [
  | base → pt
  | loop i → p/two i
  ]

let c2t/transpose : s1 → s1 → torus =
  λ [
  | base →
    λ [
    | base → pt
    | loop j → p/two j
    ]

  | loop i →
    λ [
    | base → p/one i
    | loop j → square j i
    ]
  ]



let c2t (cs : s1 × s1) : torus =
  c2t/transpose (cs.fst) (cs.snd)

let t2c2t : (t : torus) → path torus (c2t (t2c t)) t =
  λ [ _ → refl ]


let c2t2c/transpose : (c0 c1 : s1) → path (s1 × s1) (t2c (c2t/transpose c0 c1)) (c0, c1) =
  λ [ _ → λ [ _ → refl ] ]

let c2t2c (cs : s1 × s1) : path (s1 × s1) (t2c (c2t cs)) cs =
  c2t2c/transpose (cs.fst) (cs.snd)


let torus/s1s1/iso : iso (s1 × s1) torus =
  ( c2t
  , t2c
  , t2c2t
  , c2t2c
  )


let torus/s1s1/equiv : equiv (s1 × s1) torus =
  iso→equiv (s1 × s1) torus torus/s1s1/iso

let torus/s1s1/path : path^1 type (s1 × s1) torus =
  ua (s1 × s1) torus torus/s1s1/equiv
