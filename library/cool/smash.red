import prelude
import cool.pointed

data (X Y : ptype) ⊢ smash where
| basel
| baser
| proj (a : X .fst) (b : Y .fst)
| gluel (b : Y .fst) (i : 𝕀) [i=0 → basel | i=1 → proj (X .snd) b ]
| gluer (a : X .fst) (i : 𝕀) [i=0 → baser | i=1 → proj a (Y .snd) ]

def psmash (X Y : ptype) : ptype =
  (smash X Y, proj (X .snd) (Y .snd))

def flip (X Y : ptype) : smash X Y → smash Y X =
  elim [
  | basel → baser
  | baser → basel
  | proj a b → proj b a
  | gluel b i → gluer b i
  | gluer a i → gluel a i
  ]

def flip/involutive (X Y : ptype) : (s : smash X Y) → path (smash X Y) (flip Y X (flip X Y s)) s =
  elim [* → refl]

-- versions of glue* that treat (proj (X .snd) (Y .snd)) as the basepoint

def proj/gluel (X Y : ptype) (b : Y .fst)
  : path (smash X Y) (proj (X .snd) b) (proj (X .snd) (Y .snd)) =
  λ i →
  comp 0 1 (gluel (Y .snd) i) [
  | i=0 j → gluel b j
  | i=1 → refl
  ]

def proj/gluer (X Y : ptype) (a : X .fst)
  : path (smash X Y) (proj a (Y .snd)) (proj (X .snd) (Y .snd)) =
  λ i →
  comp 0 1 (gluer (X .snd) i) [
  | i=0 j → gluer a j
  | i=1 → refl
  ]

def proj/coh (X Y : ptype)
  : path (path (smash X Y) (proj (X .snd) (Y .snd)) (proj (X .snd) (Y .snd))) (proj/gluel X Y (Y .snd)) (proj/gluer X Y (X .snd))
  =
  let face (k m : dim) : smash X Y =
    comp 1 k (proj (X .snd) (Y .snd)) [
    | m=0 k → gluel (Y .snd) k
    | m=1 k → gluer (X .snd) k
    ]
  in
  λ j i →
  comp 0 1 (face i j) [
  | i=0 k → face k j
  | i=1 → refl
  | j=0 k →
    comp 0 k (gluel (Y .snd) i) [
    | i=0 k → gluel (Y .snd) k
    | i=1 → refl
    ]
  | j=1 k →
    comp 0 k (gluer (X .snd) i) [
    | i=0 k → gluer (X .snd) k
    | i=1 → refl
    ]
  ]

-- definition of the associator

def associate/proj (X Y Z : ptype) (c : Z .fst) : smash X Y → smash X (psmash Y Z) =
  elim [
  | basel → basel
  | baser → baser
  | proj a b → proj a (proj b c)
  | gluel b i → gluel (proj b c) i
  | gluer a i → 
    comp 1 0 (proj a (proj (Y .snd) (Z .snd))) [
    | i=0 k → gluer a k
    | i=1 k → proj a (proj/gluel Y Z c k)
    ]
  ]

def baser-basel (X Y : ptype) : path (smash X Y) baser basel =
  λ i →
  comp 1 0 (proj (X .snd) (Y .snd)) [
  | i=0 j → gluer (X .snd) j
  | i=1 j → gluel (Y .snd) j
  ]

def associate/gluer (X Y Z : ptype) : (s : smash X Y)
  → path (smash X (psmash Y Z)) baser (associate/proj X Y Z (Z .snd) s)
  =
  elim [
  | basel → λ i → baser-basel X (psmash Y Z) i
  | baser → refl
  | proj a b → λ i →
    comp 1 0 (proj a (proj (Y .snd) (Z .snd))) [
    | i=0 k → gluer a k
    | i=1 k → proj a (proj/gluer Y Z b k)
    ]
  | gluel b j → λ i →
    comp 1 0 (proj (X .snd) (proj (Y .snd) (Z .snd))) [
    | i=0 k → gluer (X .snd) k
    | i=1 k →
      comp 0 1 (gluel (gluer (Y .snd) k) j) [
      | j=0 m → connection/and (smash X (psmash Y Z)) (λ n → gluel (proj (Y .snd) (Z .snd)) n) k m
      | j=1 m →
        proj (X .snd)
          (comp 0 m (gluer (Y .snd) k) [
           | k=0 m → gluer b m
           | k=1 → refl
           ])
      | k=0 m → gluel (gluer b m) j
      | k=1 m → connection/or (smash X (psmash Y Z)) (λ v → gluel (proj (Y .snd) (Z .snd)) v) j m
      ]
    ]
  | gluer a j → λ i →
    comp 0 1 (connection/and (smash X (psmash Y Z)) (λ n → associate/proj X Y Z (Z .snd) (gluer a n)) i j) [
    | ∂[i] | j=0 → refl
    | j=1 k →
      comp 1 0 (proj a (proj (Y .snd) (Z .snd))) [
      | i=0 m → gluer a m
      | i=1 m → proj a (proj/coh Y Z k m)
      ]
    ]
  ]

def associate (X Y Z : ptype) : smash (psmash X Y) Z → smash X (psmash Y Z) =
  elim [
  | basel → basel
  | baser → baser
  | proj s c → associate/proj X Y Z c s
  | gluel c i → gluel (proj (Y .snd) c) i
  | gluer s i → associate/gluer X Y Z s i
  ]
