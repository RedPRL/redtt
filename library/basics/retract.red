import prelude
import isotoequiv

def is-section (A B : type) (f : A → B) : type =
  (g : B → A) × (a : A) → path A (g (f a)) a

def retract (A B : type) : type =
  (f : A → B) × is-section A B f

def retract/path-action (A B : type)
  (f : A → B) (f/sec : is-section A B f) (a a' : A)
  : retract (path _ a a') (path B (f a) (f a'))
  =
  let (g,α) = f/sec in
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
    | hsuc (l → l/ih) → λ A B (f,sec) B/level a a' →
      l/ih (path _ a a') (path B (f a) (f a'))
        (retract/path-action A B f sec a a')
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
  

