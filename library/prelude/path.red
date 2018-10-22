def pathd (A : 𝕀 → type) (M : A 0) (N : A 1) : type =
  [i] A i [
  | i=0 → M
  | i=1 → N
  ]


def path (A : type) (M N : A) : type =
  [i] A [
  | i=0 → M
  | i=1 → N
  ]

def square
  (A : type)
  (M N : 𝕀 → A)
  (O : path A (M 0) (N 0))
  (P : path A (M 1) (N 1))
  : type
  =
  [i j] A [
  | j=0 → M i
  | j=1 → N i
  | i=0 → O j
  | i=1 → P j
  ]

def funext
  (A : type)
  (B : A → type)
  (f g : (x : A) → B x)
  (p : (x : A) → path (B x) (f x) (g x))
  : path ((x : A) → B x) f g
  =
  λ i x →
  p _ i


def symm/filler (A : type) (p : 𝕀 → A) (j i : 𝕀) : A =
  comp 0 j (p 0) [
  | i=0 → p
  | i=1 → refl
  ]

def symm (A : type) (p : 𝕀 → A) : path A (p 1) (p 0) =
  symm/filler _ p 1

def symm/unit (A : type) (a : A) : path (path _ a a) refl (symm _ (λ _ → a)) =
  symm/filler _ (λ _ → a)

def trans/filler (A : type) (p : 𝕀 → A) (q : [i] A [i=0 → p 1]) (j i : 𝕀) : A =
  comp 0 j (p i) [
  | i=0 → refl
  | i=1 → q
  ]

def trans (A : type) (p : 𝕀 → A) (q : [i] A [i=0 → p 1]) : path _ (p 0) (q 1) =
  trans/filler _ p q 1


def trans/unit/r (A : type) (p : 𝕀 → A) : path (path _ (p 0) (p 1)) p (trans _ p (λ _ → p 1)) =
  trans/filler _ p (λ _ → p 1)

def trans/unit/l (A : type) (p : 𝕀 → A) : path (path _ (p 0) (p 1)) p (trans _ (λ _ → p 0) p) =
  λ k i →
  comp 0 1 (p 0) [
  | k=0 j →
    comp 0 1 (p 0) [
    | j=1 l → comp 0 i (p 0) [ l=0 → refl | l=1 → p ]
    | i=1 l → comp 0 j (p 0) [ l=0 → refl | l=1 → p ]
    | j=0 | i=0 → refl
    ]
  | i=0 → refl
  | i=1 → p
  ]


-- This proof gets simpler when dead tubes are deleted!
def trans/sym/r (A : type) (p : 𝕀 → A) : path (path _ (p 0) (p 0)) refl (trans _ p (symm _ p)) =
  λ k i →
  comp 0 1 (p i) [
  | i=0 → refl
  | i=1 → symm A p
  | k=0 → symm/filler A p i
  -- | k=1 j → trans/filler A p (symm A p) j i
  ]

def trans/sym/l (A : type) (p : 𝕀 → A) : path (path _ (p 1) (p 1)) refl (trans _ (symm _ p) p) =
  λ k i →
  comp 0 1 (symm/filler A p k i) [
  | i=0 j →
    comp 0 1 (p 1) [
    | j=0 l → comp 1 k (p 1) [ l=0 → refl | l=1 → p ]
    | k=0 l → comp 1 j (p 1) [ l=0 → refl | l=1 → p ]
    | j=1 | k=1 → refl
    ]
  | i=1 → p
  | k=0 → p
  -- | k=1 j → trans/filler A (symm A p) p j i
  ]

def J (A : type) (p : 𝕀 → A) (C : [i] A [i=0 → p 0] → type) (d : C refl) : C p =
  coe 0 1 d in λ i →
  C (λ j → comp 0 j (p 0) [i=0 → refl | i=1 → p])

def J/eq
  (A : type) (a : A)
  (C : [i] A [i=0 → a] → type) (d : C refl)
  : path (C refl) (J _ (λ _ → a) C d) d
  =
  let square (i j : 𝕀) : A = comp 0 j a [∂[i] → refl] in
  λ k →
  let mot (i : 𝕀) = C (λ j → comp 0 j a [k=0 → square i | k=1 | ∂[i] → refl]) in
  comp 0 1 d in mot [
  | k=0 → λ i → coe 0 i d in λ j → C (square j)
  | k=1 → refl
  ]

quit

-- Perhaps we could parallelize this proof? ;)
def symmd (A : 𝕀 → type) (p : (i : 𝕀) → A i) : pathd (symm^1 _ A) (p 1) (p 0) =
  λ i →
  comp 0 1 (p 0) in λ j → symm/filler^1 _ A j i [
  | i=0 → p
  | i=1 → refl
  ]
