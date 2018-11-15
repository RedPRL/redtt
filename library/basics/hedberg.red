import prelude
import basics.retract
import data.void
import data.or

def stable (A : type) : type =
  neg (neg A) → A

def dec (A : type) : type =
  or A (neg A)

def discrete (A : type) : type =
  (x y : A) → dec (path A x y)

def dec→stable (A : type) : dec A → stable A =
  elim [
  | inl a → λ _ → a
  | inr f → λ g → elim (g f) []
  ]

def neg/is-prop-over (A : 𝕀 → type)
  : is-prop-over (λ i → neg (A i))
  = prop→prop-over (λ i → neg (A i)) (neg/prop (A 1))

-- Hedberg's theorem for stable path types
def paths-stable→set (A : type) (st : (x y : A) → stable (path A x y)) : is-set A =
  λ a b p q i j →
  let square (k m : 𝕀) : A =
    comp 0 k a [
    | m=0 → p
    | m=1 → q
    ]
  in
  let cap (k m : 𝕀) = st (p k) (q k) (λ c → c (square k)) m in
  comp 0 1 (cap j i) [
  | i=0 k →
    st (p j) (p j)
       (neg/is-prop-over (λ j → neg (path A (p j) (p j)))
         (λ c → c (square 0))
         (λ c → c (square 1))
         j)
       k
  | i=1 → refl
  | ∂[j] k → weak-connection/or A (cap j) i k
  ]

-- Hedberg's theorem for decidable path types
def discrete→set (A : type) (d : discrete A) : is-set A =
  paths-stable→set A (λ x y → dec→stable (path A x y) (d x y))

def mere-relation/set-equiv 
  (A : type) (R : A → A → type) 
  (R/prop : (x y : A) → is-prop (R x y))
  (R/refl : (x : A) → R x x) 
  (R/id : (x y : A) → R x y → path A x y) 
  : (is-set A) × ((x y : A) → equiv (R x y) (path A x y))
  = 
  let eq = path-retract/equiv A R (λ a b → 
    ( R/id a b
    , λ p → coe 0 1 (R/refl a) in λ j → R a (p j)
    , λ rab → R/prop a b (coe 0 1 (R/refl a) in λ j → R a (R/id a b rab j)) rab
    )) in
  ( λ x y → coe 0 1 (R/prop x y) in λ j → is-prop (ua _ _ (eq x y) j)
  , eq 
  )

-- Hedberg's theorem is a corollary of above
def paths-stable→set/alt (A : type) (st : (x y : A) → stable (path A x y)) : is-set A =
  (mere-relation/set-equiv A (λ x y → neg (neg (path A x y)))
    (λ x y → neg/prop (neg (path A x y)))
    (λ _ np → np refl)
    st
).fst