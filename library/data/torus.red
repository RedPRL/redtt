data torus where
| pt
| p/one (i : 𝕀) [∂[i] → pt]
| p/two (i : 𝕀) [∂[i] → pt]
| square (i j : 𝕀)
  [ ∂[i] → p/one j
  | ∂[j] → p/two i
  ]
