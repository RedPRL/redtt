import prelude
import data.void
import data.unit
import data.list
import basics.retract
import paths.sigma

def list/code (A : type) : list A → list A → type =
  elim [
  | nil →
    elim [
    | nil → unit
    | cons _ _ → void
    ]
  | cons x (xs → code/xs) →
    elim [
    | nil → void
    | cons y ys → path A x y × code/xs ys
    ]
  ]

def list/refl (A : type) : (xs : list A) → list/code A xs xs =
  elim [
  | nil → triv
  | cons x (xs → refl/xs) → (refl, refl/xs)
  ]

def list/encode (A : type) (xs ys : list A) (q : path (list A) xs ys) : list/code A xs ys =
  coe 0 1 (list/refl A xs) in λ i → list/code A xs (q i)

def list/encode/refl (A : type) (xs : list A)
  : path (list/code A xs xs) (list/encode A xs xs refl) (list/refl A xs)
  =
  λ i → coe i 1 (list/refl A xs) in λ i → list/code A xs xs

def list/decode (A : type) : (xs ys : list A) → list/code A xs ys → path (list A) xs ys =
  elim [
  | nil →
    elim [
    | nil → refl
    | cons _ _ → elim []
    ]
  | cons x (xs → decode/xs) →
    elim [
    | nil → elim []
    | cons y ys → λ (p, c) i → cons (p i) (decode/xs ys c i)
    ]
  ]

def list/decode/refl (A : type)
  : (xs : list A) → path (path (list A) xs xs) (list/decode A xs xs (list/refl A xs)) refl
  =
  elim [
  | nil → refl
  | cons x (xs → decode/refl/xs) → λ i j → cons x (decode/refl/xs i j)
  ]

def list/decode-encode/refl (A : type) (xs : list A)
  : path (path (list A) xs xs) (list/decode A xs xs (list/encode A xs xs refl)) refl
  =
  trans (path (list A) xs xs)
    (λ i → list/decode A xs xs (list/encode/refl A xs i))
    (list/decode/refl A xs)

def list/decode-encode (A : type) (xs ys : list A) (q : path (list A) xs ys)
  : path (path (list A) xs ys) (list/decode A xs ys (list/encode A xs ys q)) q
  =
  J _ q
    (λ q → path (path (list A) xs (q 1)) (list/decode A xs (q 1) (list/encode A xs (q 1) q)) q)
    (list/decode-encode/refl A xs)

def list/encode/cons (A : type) (x y : A) (p : path A x y) (xs ys : list A) (q : path (list A) xs ys)
  : path (list/code A (cons x xs) (cons y ys))
    (list/encode A (cons x xs) (cons y ys) (λ i → cons (p i) (q i)))
    (p, list/encode A xs ys q)
  =
  λ i →
  coe i 1
    ( λ j → weak-connection/and A p i j
    , coe 0 i (list/refl A xs) in λ i → list/code A xs (q i)
    )
  in
  λ i → list/code A (cons x xs) (cons (p i) (q i))

def list/encode-decode (A : type)
  : (xs ys : list A) (c : list/code A xs ys)
    → path (list/code A xs ys) (list/encode A xs ys (list/decode A xs ys c)) c
  =
  elim [
  | nil →
    elim [
    | nil → elim [triv → refl]
    | cons _ _ → elim []
    ]
  | cons x (xs → encode-decode/xs) →
    elim [
    | nil → elim []
    | cons y ys → λ (p, c) →
      trans (path A x y × list/code A xs ys)
        (list/encode/cons A x y p xs ys (list/decode A xs ys c))
        (λ i → (p, encode-decode/xs ys c i))
    ]
  ]

-- list preserves hlevels >= set

def list/code/hlevel (l : hlevel) (A : type) (A/level : has-hlevel (hsuc (hsuc l)) A)
  : (xs ys : list A) → has-hlevel (hsuc l) (list/code A xs ys)
  =
  elim [
  | nil → elim [
    | nil → prop→hlevel l unit unit/prop
    | cons y ys → prop→hlevel l void void/prop
    ]
  | cons x (xs → xs/ih) → elim [
    | nil → prop→hlevel l void void/prop
    | cons y ys →
      sigma/hlevel (hsuc l) (path A x y) (λ _ → list/code A xs ys)
        (A/level x y)
        (λ _ → xs/ih ys)
    ]
  ]

def list/hlevel (l : hlevel) (A : type) (A/level : has-hlevel (hsuc (hsuc l)) A)
  : has-hlevel (hsuc (hsuc l)) (list A) =
  elim [
  | nil → elim [
    | nil →
      retract/hlevel (hsuc l)
        (path (list A) nil nil)
        unit
        (list/encode A nil nil, list/decode A nil nil, ?)
        ?
    | cons y ys → ?
    ]
  | cons x xs → ?
  ]

