import prelude

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
