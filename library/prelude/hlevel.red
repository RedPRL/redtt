import prelude.path
import prelude.connection

def is-contr (C : type) : type =
  (c : _) × (c' : _) → path C c' c

/-
let is-param-contr-over (A : type) (B : A → type) : type =
  (c : (a : _) → B a) × (a : 𝕀 → A) (c' : B (a 0)) → pathd (λ i → B (a i)) c' (c (a 1))
-/

def is-prop (C : type) : type =
  (c c' : _)
  → path C c c'

data hlevel where
| contr
| hsuc (l : hlevel)

def has-hlevel : hlevel → type → type =
  elim [
  | contr → is-contr
  | hsuc l →
    elim l [
    | contr → is-prop
    | hsuc (l → l/ih) → λ A → (a a' : A) → l/ih (path _ a a')
    ]
  ]

def prop : hlevel = hsuc contr
def set : hlevel = hsuc prop
def groupoid : hlevel = hsuc set

def is-set = has-hlevel set
def is-groupoid = has-hlevel groupoid

def type/of-level (l : hlevel) : type^1 = (A : type) × has-hlevel l A
def type/prop = type/of-level prop
def type/set = type/of-level set
def type/groupoid = type/of-level groupoid

-- lower hlevels imply higher hlevels

def prop→set (A : type) (A/prop : is-prop A) : is-set A =
  λ a b p q i j →
  comp 0 1 a [
  | ∂[j] → A/prop a (p j)
  | i=0 → A/prop a (p j)
  | i=1 → A/prop a (q j)
  ]

def raise-hlevel : (l : hlevel) (A : type) → has-hlevel l A → has-hlevel (hsuc l) A =
  elim [
  | contr → λ A A/level a a' →
    trans A (A/level .snd a) (symm A (A/level .snd a'))
  | hsuc l →
    elim l [
    | contr → prop→set
    | hsuc (l → l/ih) → λ A A/level a a' → l/ih (path _ a a') (A/level a a')
    ]
  ]

def prop→hlevel : (l : hlevel) (A : type) → is-prop A → has-hlevel (hsuc l) A =
  elim [
  | contr → λ _ A/prop → A/prop
  | hsuc (l → l/ih) → λ A A/prop → raise-hlevel (hsuc l) A (l/ih A A/prop)
  ]

-- propositional type lines

def is-prop-over (A : 𝕀 → type) : type =
  (a : A 0) → (b : A 1) → pathd A a b

def prop→prop-over (A : 𝕀 → type) (p : is-prop (A 1))
  : is-prop-over A
  =
  λ a b i →
    comp 0 1 (coe 0 i a in A) [
    | i=0 → refl
    | i=1 → p (coe 0 1 a in A) b
    ]

-- hlevel of path types

def path/hlevel : (l : hlevel) (A : type)
  (A/level : has-hlevel (hsuc l) A) (a a' : A)
  → has-hlevel l (path _ a a')
  =
  elim [
  | contr → λ A A/prop a a' →
    (A/prop a a', λ p → prop→set A A/prop a a' p (A/prop a a'))
  | hsuc l → λ A A/level a a' → A/level a a'
  ]

def pathd/hlevel (l : hlevel) (A : type) (B : A → type) (p : 𝕀 → A)
  (B/level : has-hlevel (hsuc l) (B (p 1)))
  (b : B (p 0)) (b' : B (p 1))
  : has-hlevel l (pathd (λ i → B (p i)) b b')
  =
  coe 1 0
    (path/hlevel l (B (p 1)) B/level (coe 0 1 b in λ j → B (p j)) b')
    in λ i →
      has-hlevel l
        (pathd (λ j → weak-connection/or^1 type (λ n → B (p n)) i j)
          (coe 0 i b in λ j → B (p j))
          b')

def path/based/contr (A : type) (a : A)
  : is-contr ((x : _) × path _ a x) =
  ( (a, refl)
  , λ x i →
    ( comp 0 1 a [
      | i=0 → x.snd
      | i=1 → refl
      ]
    , λ j →
      comp 0 j a [
      | i=0 → x.snd
      | i=1 → refl
      ]
    )
  )
