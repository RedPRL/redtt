import bool
import isotoequiv

def ptype : type^1 = (A : type) × A

def pmap (pA pB : ptype) : type =
  (f : pA.fst → pB.fst) × path _ (f (pA.snd)) (pB.snd)

def p→ (pA pB : ptype) : ptype =
  (pmap pA pB, λ _ → pB.snd, refl)

def pequiv (pA pB : ptype) : type =
  (f : pmap pA pB) × is-equiv (pA.fst) (pB.fst) (f.fst)

def pbool : ptype = (bool, ff)

def pf (pA : ptype) : pequiv (p→ pbool pA) pA =
  let fwd : pmap (p→ pbool pA) pA =
    (λ f → f.fst tt , refl)
  in

  let bwd (a : pA.fst) : pmap pbool pA =
    ( elim [ tt → a | ff → pA.snd ]
    , refl
    )
  in

  let bwdfwd (f : pmap pbool pA) : path _ (bwd (fwd.fst f)) f =
    let bwdfwd/pt (i j : dim) : pA.fst =
      comp 1 j (pA.snd) [
      | i=0 → refl
      | i=1 → f.snd
      ]
    in
    let bwdfwd/map : (b : bool) → path _ (bwd (fwd.fst f) .fst b) (f.fst b) =
      elim [
      | tt → refl
      | ff → λ i → bwdfwd/pt i 0
      ]
    in
    λ i → (λ b → bwdfwd/map b i, bwdfwd/pt i)
  in
  (fwd, iso→equiv _ _ (fwd.fst, bwd, refl, bwdfwd) .snd)

def pΩ (pA : ptype) : ptype =
  ( path _ (pA.snd) (pA.snd)
  , refl
  )

def pΩ/map (pA pB : ptype) (pf : pmap pA pB) : pmap (pΩ pA) (pΩ pB) =
  ( λ p i → comp 0 1 (pf.fst (p i)) [∂[i] → pf.snd]
  , λ j i → comp j 1 (pf.snd j) [∂[i] → pf.snd]
  )

def pΩ/map/trans (pA pB : ptype) (pf : pmap pA pB) (p q : pΩ pA .fst)
  : path _
    (pΩ/map pA pB pf .fst (trans _ p q))
    (trans _
     (pΩ/map pA pB pf .fst p)
     (pΩ/map pA pB pf .fst q))
  =
  let face : [i j] (pB.fst) [i=0 → pB.snd] =
    λ i j →
    comp 0 1 (pf .fst (comp 0 j (p i) [i=0 → refl | i=1 → q]))
      [ i=0 → pf.snd
      | i=1 k → comp 0 k (pf .fst (q j)) [∂[j] → pf.snd]
      ]
  in
  λ k i →
  comp 0 1 (face i 0) [
  | i=0 j → pB.snd
  | (k=0 | i=1) j → face i j
  ]
