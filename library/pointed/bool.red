import prelude
import data.bool
import basics.isotoequiv

def pbool : ptype = (bool, tt)

def from-pbool (pA : ptype) : pequiv (p→ pbool pA) pA =
  let fwd : pmap (p→ pbool pA) pA =
    (λ f → f.fst ff , refl)
  in

  let bwd (a : pA.fst) : pmap pbool pA =
    ( elim [ tt → pA.snd | ff → a ]
    , refl
    )
  in

  let bwdfwd (f : pmap pbool pA) : path _ (bwd (fwd.fst f)) f =
    let bwdfwd/pt (i j : 𝕀) : pA.fst =
      comp 1 j (pA.snd) [
      | i=0 → refl
      | i=1 → f.snd
      ]
    in
    let bwdfwd/map : (b : bool) → path _ (bwd (fwd.fst f) .fst b) (f.fst b) =
      elim [
      | tt → λ i → bwdfwd/pt i 0
      | ff → refl
      ]
    in
    λ i → (λ b → bwdfwd/map b i, bwdfwd/pt i)
  in
  (fwd, iso→equiv _ _ (fwd.fst, bwd, refl, bwdfwd) .snd)
