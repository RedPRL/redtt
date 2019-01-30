import prelude
import basics.isotoequiv

def retraction (A B : type) (f : A → B) : type =
  (g : B → A) × (a : A) → path A (g (f a)) a

def section (A B : type) (f : A → B) : type =
  (g : B → A) × (b : B) → path B (f (g b)) b

def retract (A B : type) : type =
  (f : A → B) × retraction A B f

def retract/path-action (A B : type)
  (f : A → B) (retr : retraction A B f) (a a' : A)
  : retract (path _ a a') (path B (f a) (f a'))
  =
  let (g,α) = retr in
  ( λ p i → f (p i)
  , λ q i → comp 0 1 (g (q i)) [i=0 → α a | i=1 → α a']
  , λ p j i → comp j 1 (α (p i) j) [i=0 → α a | i=1 → α a']
  )

def retract/hlevel : (l : hlevel) (A B : type)
  → retract A B → has-hlevel l B → has-hlevel l A
  =
  elim [
  | contr → λ A B (f,g,α) B/contr →
    ( g (B/contr .fst)
    , λ a i →
      comp 0 1 (g (B/contr .snd (f a) i)) [
      | i=0 → α a
      | i=1 → refl
      ]
    )
  | hsuc l →
    elim l [
    | contr → λ A B (f,g,α) B/prop a a' i →
      comp 0 1 (g (B/prop (f a) (f a') i)) [
      | i=0 → α a
      | i=1 → α a'
      ]
    | hsuc (l → l/ih) → λ A B (f,retr) B/level a a' →
      l/ih (path _ a a') (path B (f a) (f a'))
        (retract/path-action A B f retr a a')
        (B/level (f a) (f a'))
    ]
  ]

-- Adapted from https://github.com/HoTT/book/issues/718
-- Any family of retracts of the path family preserves refl through the other round-trip
def path-retract/preserves-refl (A : type) (R : A → A → type)
  (ret : (x y : A) → retract (R x y) (path A x y)) (x : A)
  : path _ (ret x x .fst (ret x x .snd .fst refl)) refl
  =
  let s (x y : A) : R x y → path A x y = ret x y .fst in
  let r (x y : A) : path A x y → R x y = ret x y .snd .fst in
  let q = s x x (r x x refl) in
  let cap1 : [i j] A [
    | j=0 → x
    | j=1 → q i
    | i=0 → q j
    | i=1 → s x x (r x x q) j
    ]
    =
    λ i j →
    s x (q i) (r x (q i) (λ k → weak-connection/and A q i k)) j
  in
  let cap2 : [i j] A [
    | j=0 → x
    | j=1 → q i
    | ∂[i] → q j
    ]
    =
    λ i j →
    comp 0 1 (cap1 i j) [
    | ∂[j] | i=0 → refl
    | i=1 k → s x x (ret x x .snd .snd (r x x refl) k) j
    ]
  in
  let face (m k : 𝕀) : A =
    comp 0 m x [
    | k=0 → q
    | k=1 → refl
    ]
  in
  λ i j →
  comp 0 1 (cap2 i j) [
  | j=0 | i=0 → refl
  | j=1 → face i
  | i=1 → face j
  ]

-- a family of retracts of the path family gives rise to a family of equivalences

def path-retract/equiv (A : type) (R : A → A → type)
  (ret : (x y : A) → retract (R x y) (path A x y)) (a b : A)
  : equiv (R a b) (path A a b)
  =
  let preserves-refl = path-retract/preserves-refl A R ret a in
  iso→equiv (R a b) (path A a b)
    ( ret a b .fst
    , ret a b .snd .fst
    , λ p → J A p (λ q → path _ (ret a (q 1) .fst (ret a (q 1) .snd .fst q)) q) preserves-refl
    , ret a b .snd .snd
    )

def equiv-section/prop (A B : type) (f : A → B) (c : is-equiv A B f)
  : is-prop (section A B f) =
  λ (g0,p0) (g1,p1) i →
  let α (b : B) : path (fiber A B f b) (g0 b, p0 b) (g1 b, p1 b) =
    contr→prop (fiber A B f b) (c b) (g0 b, p0 b) (g1 b, p1 b)
  in
  (λ b → α b i .fst, λ b → α b i .snd)

-- TODO this does not really belong in this file
def precompose-equiv (A B C : type) (e : equiv A B) : equiv (B → C) (A → C) =
  let (f,g,α,β) = equiv→iso _ _ e in
  iso→equiv (B → C) (A → C)
    ( λ h a → h (f a)
    , λ k b → k (g b)
    , λ k i a → k (β a i)
    , λ h i b → h (α b i)
    )

def equiv-retraction/prop (A B : type) (f : A → B) (c : is-equiv A B f)
  : is-prop (retraction A B f) =
  λ (g0,q0) (g1,q1) i →
  let p =
    contr→prop _ (precompose-equiv A B A (f,c) .snd (λ a → a))
      (g0, λ j b → q0 b j) (g1, λ j b → q1 b j)
  in
  (p i .fst, λ b j → p i .snd j b)
