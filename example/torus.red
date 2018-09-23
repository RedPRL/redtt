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
  elim [
  | pt → (base, base)
  | p/one i → (loop i, base)
  | p/two i → (base, loop i)
  | square i j → (loop j, loop i)
  ]

let c2t : (s1 × s1) → torus =
  λ [,] →                   -- now the goal is s1 → s1 → torus
  elim [                    -- now the goal is s1 → torus
  | base →
    elim [
    | base → pt
    | loop j → p/two j
    ]
  | loop i →
    elim [
    | base → p/one i
    | loop j → square j i
    ]
  ]

let t2c2t : (t : torus) → path torus (c2t (t2c t)) t =
  -- wildcard patterns call the elimination tactic, with the rhs in all cases
  λ * → refl

let c2t2c : (cs : s1 × s1) → path (s1 × s1) (t2c (c2t cs)) cs =
  -- combination of wildcard pattern with sigma type inversion pattern
  λ (*, *) → refl

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
