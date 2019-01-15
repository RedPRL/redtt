import prelude

data (X Y : ptype) ⊢ smash where
| basel
| baser
| proj (a : X .fst) (b : Y .fst)
| gluel (b : Y .fst) (i : 𝕀) [i=0 → basel | i=1 → proj (X .snd) b ]
| gluer (a : X .fst) (i : 𝕀) [i=0 → baser | i=1 → proj a (Y .snd) ]

def smash/map (X Y Z W : ptype) (f : pmap X Z) (g : pmap Y W) : smash X Y → smash Z W =
  elim [
  | basel → basel
  | baser → baser
  | proj a b → proj (f .fst a) (g .fst b)
  | gluel b i → comp 1 0 (gluel (g .fst b) i) [i=0 → refl | i=1 j → proj (f .snd j) (g .fst b) ]
  | gluer a i → comp 1 0 (gluer (f .fst a) i) [i=0 → refl | i=1 j → proj (f .fst a) (g .snd j) ]
  ]
