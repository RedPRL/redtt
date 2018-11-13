import prelude
import data.bool
import basics.pointed
import basics.isotoequiv

data (X Y : ptype) ⊢ smash where
| basel
| baser
| proj (a : X .fst) (b : Y .fst)
| gluel (b : Y .fst) (i : 𝕀) [i=0 → basel | i=1 → proj (X .snd) b ]
| gluer (a : X .fst) (i : 𝕀) [i=0 → baser | i=1 → proj a (Y .snd) ]

def psmash (X Y : ptype) : ptype =
  (smash X Y, proj (X .snd) (Y .snd))

def smash/map (X Y Z W : ptype) (f : pmap X Z) (g : pmap Y W) : smash X Y → smash Z W =
  elim [
  | basel → basel
  | baser → baser
  | proj a b → proj (f .fst a) (g .fst b)
  | gluel b i → comp 1 0 (gluel (g .fst b) i) [i=0 → refl | i=1 j → proj (f .snd j) (g .fst b) ]
  | gluer a i → comp 1 0 (gluer (f .fst a) i) [i=0 → refl | i=1 j → proj (f .fst a) (g .snd j) ]
  ]

def commute (X Y : ptype) : smash X Y → smash Y X =
  elim [
  | basel → baser
  | baser → basel
  | proj a b → proj b a
  | gluel b i → gluer b i
  | gluer a i → gluel a i
  ]

def commute/equiv (X Y : ptype) : equiv (smash X Y) (smash Y X) =
  iso→equiv _ _ (commute X Y, commute Y X, elim [* → refl], elim [* → refl])

-- pivot helper functions

def pivotl/filler (X Y : ptype) (b b' : Y .fst) (j i : 𝕀) : smash X Y =
  comp 0 j (gluel b' i) [
  | i=0 j → gluel b j
  | i=1 → refl
  ]

def pivotl (X Y : ptype) (b b' : Y .fst)
  : path (smash X Y) (proj (X .snd) b) (proj (X .snd) b')
  =
  pivotl/filler X Y b b' 1

def pivotr/filler (X Y : ptype) (a a' : X .fst) (j i : 𝕀) : smash X Y =
  comp 0 j (gluer a' i) [
  | i=0 j → gluer a j
  | i=1 → refl
  ]

def pivotr (X Y : ptype) (a a' : X .fst)
  : path (smash X Y) (proj a (Y .snd)) (proj a' (Y .snd))
  =
  pivotr/filler X Y a a' 1

def pivot-coh (X Y : ptype)
  : path (path (smash X Y) (proj (X .snd) (Y .snd)) (proj (X .snd) (Y .snd)))
    (pivotr X Y (X .snd) (X .snd)) (pivotl X Y (Y .snd) (Y .snd))
  =
  let face (k m : 𝕀) : smash X Y =
    comp 1 k (proj (X .snd) (Y .snd)) [
    | m=0 k → gluer (X .snd) k
    | m=1 k → gluel (Y .snd) k
    ]
  in
  λ j i →
  comp 0 1 (face i j) [
  | i=0 k → face k j
  | i=1 → refl
  ]

def basel-baser/filler (X Y : ptype) (j i : 𝕀) : smash X Y =
  comp 1 j (gluel (Y .snd) i) [
  | i=0 → refl
  | i=1 j → gluer (X .snd) j
  ]

def basel-baser (X Y : ptype) : path (smash X Y) basel baser = basel-baser/filler X Y 0

def pivotlr (X Y : ptype) (b : Y .fst) (a : X .fst)
  : path (smash X Y) (proj (X .snd) b) (proj a (Y .snd))
  =
  λ i →
  comp 0 1 (basel-baser X Y i) [
  | i=0 j → gluel b j
  | i=1 j → gluer a j
  ]

-- unit laws

def unitr (X : ptype) : smash X pbool → X .fst =
  let out/proj (a : X .fst) : bool → X .fst =
    elim [tt → a | ff → X .snd]
  in
  let out/gluel : (b : bool) → path (X .fst) (X .snd) (out/proj (X .snd) b) =
    elim [* → refl]
  in
  elim [
  | proj a b → out/proj a b
  | gluel b i → out/gluel b i
  | * → X .snd
  ]

def unitr/in-out (X : ptype) : (s : smash X pbool) → path (smash X pbool) (proj (unitr X s) tt) s =
  let in-out/basel : path (smash X pbool) (proj (X .snd) tt) basel =
    λ j →
    comp 0 1 basel [
    | j=0 k → gluel tt k
    | j=1 → refl
    ]
  in
  let in-out/baser : path (smash X pbool) (proj (X .snd) tt) baser =
    λ j →
    comp 0 1 (basel-baser X pbool j) [
    | j=0 k → gluel tt k
    | j=1 → refl
    ]
  in
  let in-out/proj (a : X .fst)
    : (b : bool) → path (smash X pbool) (proj (unitr X (proj a b)) tt) (proj a b)
    =
    elim [
    | tt → refl
    | ff → pivotlr X pbool tt a
    ]
  in
  let in-out/gluel : (b : bool) → [i j] smash X pbool [
    | i=0 → in-out/basel j
    | i=1 → in-out/proj (X .snd) b j
    | j=0 → proj (unitr X (gluel b i)) tt
    | j=1 → gluel b i
    ]
    =
    elim [
    | tt → λ i j →
      comp 0 1 (gluel tt i) [
      | i=1 → refl
      | j=0 k → weak-connection/or (smash X pbool) (λ v → gluel tt v) i k
      | j=1 → refl
      ]
    | ff → λ i j →
      comp 0 1 (weak-connection/and (smash X pbool) (λ n → basel-baser X pbool n) i j) [
      | j=0 k → gluel tt k
      | j=1 k → basel-baser/filler X pbool k i
      ]
    ]
  in
  let in-out/gluer (a : X .fst) : [i j] smash X pbool [
    | i=0 → in-out/baser j
    | i=1 → in-out/proj a ff j
    | j=0 → proj (X .snd) tt
    | j=1 → gluer a i
    ]
    =
    λ i j →
    comp 0 1 (basel-baser X pbool j) [
    | j=0 k → gluel tt k
    | j=1 k → weak-connection/and (smash X pbool) (λ n → gluer a n) i k
    ]
  in
  elim [
  | basel → in-out/basel
  | baser → in-out/baser
  | proj a b → in-out/proj a b
  | gluel b i → λ j → in-out/gluel b i j
  | gluer a i → λ j → in-out/gluer a i j
  ]

def unitr/equiv (X : ptype) : equiv (X .fst) (smash X pbool) =
  iso→equiv (X .fst) (smash X pbool) (λ a → proj a tt, unitr X, unitr/in-out X, λ _ → refl)

-- Definition of rearrange : (X ∧ Y) ∧ Z → (Z ∧ Y) ∧ X
-- The associator can be derived from rearrange using the commutator:
-- (X ∧ Y) ∧ Z → (Z ∧ Y) ∧ X → (Y ∧ Z) ∧ X → X ∧ (Y ∧ Z)
-- If we can show rearrange is involutive, then the associator is an equivalence

def rearrange/proj (X Y Z : ptype) (c : Z .fst) : smash X Y → smash (psmash Z Y) X =
  elim [
  | basel → baser
  | baser → basel
  | proj a b → proj (proj c b) a
  | gluel b i → gluer (proj c b) i
  | gluer a i →
    comp 1 0 (gluel a i) [
    | i=0 → refl
    | i=1 k → proj (pivotr Z Y c (Z .snd) k) a
    ]
  ]

def rearrange/gluer (X Y Z : ptype) : (s : smash X Y)
  → path (smash (psmash Z Y) X) basel (rearrange/proj X Y Z (Z .snd) s)
  =
  elim [
  | basel → λ i → basel-baser (psmash Z Y) X i
  | baser → refl
  | proj a b → λ i →
    comp 1 0 (gluel a i) [
    | i=0 → refl
    | i=1 k → proj (pivotl Z Y b (Y .snd) k) a
    ]
  | gluel b j → λ i →
    comp 1 0 (gluel (X .snd) i) [
    | i=0 k → refl
    | i=1 k →
      comp 0 1 (gluer (gluel (Y .snd) k) j) [
      | j=0 m → connection/and (smash (psmash Z Y) X) (λ n → gluer (proj (Z .snd) (Y .snd)) n) k m
      | j=1 m → proj (pivotl/filler Z Y b (Y .snd) m k) (X .snd)
      | k=0 m → gluer (gluel b m) j
      | k=1 m → connection/or (smash (psmash Z Y) X) (λ v → gluer (proj (Z .snd) (Y .snd)) v) j m
      ]
    ]
  | gluer a j → λ i →
    comp 0 1 (connection/and (smash (psmash Z Y) X) (λ n → rearrange/proj X Y Z (Z .snd) (gluer a n)) i j) [
    | ∂[i] | j=0 → refl
    | j=1 k →
      comp 1 0 (gluel a i) [
      | i=0 → refl
      | i=1 m → proj (pivot-coh Z Y k m) a
      ]
    ]
  ]

def rearrange (X Y Z : ptype) : smash (psmash X Y) Z → smash (psmash Z Y) X =
  elim [
  | basel → baser
  | baser → basel
  | proj s c → rearrange/proj X Y Z c s
  | gluel c i → gluer (proj c (Y .snd)) i
  | gluer s i → rearrange/gluer X Y Z s i
  ]

def associate (X Y Z : ptype) (t : smash (psmash X Y) Z) : smash X (psmash Y Z) =
  commute (psmash Y Z) X
    (smash/map (psmash Z Y) X (psmash Y Z) X (commute Z Y, refl) (λ x → x, refl)
      (rearrange X Y Z t))
