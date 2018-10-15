import path
import hlevel
import connection
import J
import void
import unit

-- encode-decode

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

-- list takes sets to sets

def list/set (A : type) (setA : is-set A) : is-set (list A) =
  elim [
  | nil →
    elim [
    | nil → λ p q i →
      comp 0 1 refl [
      | i=0 → list/decode-encode A nil nil p
      | i=1 → list/decode-encode A nil nil q
      ]
    | cons _ _ → λ p → elim (list/encode A _ _ p) []
    ]
  | cons x (xs → list/set/xs) →
    elim [
    | nil → λ p → elim (list/encode A _ _ p) []
    | cons y ys → λ p q i →
      let (ph,pc) = list/encode A (cons x xs) (cons y ys) p in
      let (qh,qc) = list/encode A (cons x xs) (cons y ys) q in
      let pt = list/decode A xs ys pc in
      let qt = list/decode A xs ys qc in
      comp 0 1 (λ j → cons (setA x y ph qh i j) (list/set/xs ys pt qt i j)) [
      | i=0 → list/decode-encode A (cons x xs) (cons y ys) p
      | i=1 → list/decode-encode A (cons x xs) (cons y ys) q
      ]
    ]
  ]

