import prelude
import prelude.pointed
import data.bool
import data.smash
import basics.retract
import paths.bool
import pointed.bool
import pointed.smash

-- characterization of the maps of type (X Y : ptype) → X ∧ Y →* X ∧ Y,
-- assuming a parametricity axiom about maps of type (X Y : ptype) → X → Y → X ∧ Y

-- general definitions and lemmas

def ppoint (X : ptype) (x : X .fst) : pmap pbool X =
  (elim [ tt → X .snd | ff → x ], refl)

def pconst (X Y : ptype) : pmap X Y =
  (λ _ → Y .snd , λ _ → Y .snd)

def has-square-fillers (A : type) : type =
  (p0- p1- : 𝕀 → A)
  (p-0 : path A (p0- 0) (p1- 0))
  (p-1 : path A (p0- 1) (p1- 1))
  → [i j] A [i=0 → p0- j | i=1 → p1- j | j=0 → p-0 i | j=1 → p-1 i ]

def set→has-square-fillers (A : type) (A/set : is-set A)
  : has-square-fillers A
  =
  λ p0- p1- p-0 p-1 →
  let filler (i j : 𝕀) : A = comp 0 j (p-0 i) [ i=0 → p0- | i=1 → p1- ]
  in
  λ i j →
  comp 0 1 (filler i j) [
  | i=0 | i=1 | j=0 → refl
  | j=1 k → A/set (p-1 0) (p-1 1) (λ i → filler i 1) p-1 k i
  ]

-- definition of the necessary parametricity axiom

def parametricity-ax/type : type^1 =
  (X Y : ptype) → X .fst → Y .fst → smash X Y

def parametricity-ax : type^1 =
  (f : parametricity-ax/type) (X : ptype) (Y : ptype) (x : X .fst) (y : Y .fst)
  → path (smash X Y)
    (f X Y x y)
    (smash/map pbool pbool X Y (ppoint X x) (ppoint Y y) (f pbool pbool ff ff))

-- proof of the theorem

def workhorse/options (b : bool) : parametricity-ax/type =
  λ X Y x y → smash/map pbool pbool X Y (ppoint X x) (ppoint Y y) (proj b ff)

def workhorse (α : parametricity-ax) (f : parametricity-ax/type)
  : (b : bool) × (path^1 _ f (workhorse/options b))
  =
 ( unitr pbool (f pbool pbool ff ff) 
  , λ i X Y x y →
    comp 1 0 (α f X Y x y i) [
    | i=0 → refl
    | i=1 j →
      smash/map pbool pbool X Y (ppoint X x) (ppoint Y y)
        (unitr/in-out pbool (f pbool pbool ff ff) j)
    ]
  )

def parametricity-ax/set (α : parametricity-ax) : is-set^1 parametricity-ax/type =
  retract/hlevel^1 set _ bool
    ( λ f → workhorse α f .fst
    , workhorse/options
    , λ f → symm^1 parametricity-ax/type (workhorse α f .snd)
    )
    bool/set

def main-theorem/options (b : bool) : (X Y : ptype) → pmap (psmash X Y) (psmash X Y) =
  λ X Y → elim b [ tt → pconst (psmash X Y) (psmash X Y) | ff → pidf (psmash X Y) ]

def main-theorem (α : parametricity-ax)
  (f : (X Y : ptype) → pmap (psmash X Y) (psmash X Y))
  : (b : bool) × (path^1 _ f (main-theorem/options b))
  =
  let b = workhorse α (λ X Y x y → f X Y .fst (proj x y)) .fst in
  let f' = main-theorem/options b in
  ( b
  , λ i →
    let options/proj (X Y : ptype) (x : X .fst) (y : Y .fst) : (b : bool)
      → path (smash X Y)
        (workhorse/options b X Y x y)
        (main-theorem/options b X Y .fst (proj x y))
      =
      elim [
      | tt → trans (smash X Y) (symm (smash X Y) (λ i → gluel y i)) (λ i → gluel (Y .snd) i)
      | ff → refl
      ]
    in
    let on-point (X Y : ptype)
      : path (smash X Y) (f X Y .fst (psmash X Y .snd)) (f' X Y .fst (psmash X Y .snd))
      =
      trans (smash X Y) (f X Y .snd) (symm (smash X Y) (f' X Y .snd))
    in
    let ind/basel (X Y : ptype)
      : path (smash X Y) (f X Y .fst basel) (f' X Y .fst basel)
      =
      λ i →
      comp 1 0 (on-point X Y i) [
      | i=0 k → f X Y .fst (gluel (Y .snd) k)
      | i=1 k → f' X Y .fst (gluel (Y .snd) k)
      ]
    in
    let ind/baser (X Y : ptype)
      : path (smash X Y) (f X Y .fst baser) (f' X Y .fst baser) =
      λ i →
      comp 1 0 (on-point X Y i) [
      | i=0 k → f X Y .fst (gluer (X .snd) k)
      | i=1 k → f' X Y .fst (gluer (X .snd) k)
      ]
    in
    let ind/proj (X Y : ptype) (x : X .fst) (y : Y .fst)
      : path (smash X Y) (f X Y .fst (proj x y)) (f' X Y .fst (proj x y))
      =
      trans (smash X Y)
        (λ i → workhorse α (λ X Y x y → f X Y .fst (proj x y)) .snd i X Y x y)
        (options/proj X Y x y b)
    in 
    λ X Y →
    let ind : (s : smash X Y) → path (smash X Y) (f X Y .fst s) (f' X Y .fst s)
      =
      elim [
      | basel → ind/basel X Y
      | baser → ind/baser X Y
      | proj x y → ind/proj X Y x y
      | gluel y j → λ i → 
        set→has-square-fillers^1
          parametricity-ax/type
          (parametricity-ax/set α)
          (λ j X Y _ y → f X Y .fst (gluel y j))
          (λ j X Y _ y → f' X Y .fst (gluel y j))
          (λ i X Y _ _ → ind/basel X Y i)
          (λ i X Y _ y → ind/proj X Y (X .snd) y i)
          i j X Y (X .snd) y 
      | gluer x j → λ i →
        set→has-square-fillers^1
          parametricity-ax/type
          (parametricity-ax/set α)
          (λ j X Y x _ → f X Y .fst (gluer x j))
          (λ j X Y x _ → f' X Y .fst (gluer x j))
          (λ i X Y _ _ → ind/baser X Y i)
          (λ i X Y x _ → ind/proj X Y x (Y .snd) i)
          i j X Y x (Y .snd)
      ]
    in
    ( λ s → ind s i
    , λ j →
      set→has-square-fillers^1
        parametricity-ax/type
        (parametricity-ax/set α)
        (λ j X Y _ _ → f X Y .snd j)
        (λ j X Y _ _ → f' X Y .snd j)
        (λ i X Y _ _ → ind/proj X Y (X .snd) (Y .snd) i)
        (λ i X Y _ _ → psmash X Y .snd)
        i j X Y (X .snd) (Y .snd)
    )
  )
