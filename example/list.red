import path
import connection
import J
import void
import unit

data list (A : type) where
| nil
| cons (x : A) (xs : list)

let append (A : type) : list A → list A → list A =
  elim [
  | nil → λ ys → ys
  | cons x (xs → ih) → λ ys → cons x (ih ys)
  ]

let append/idn/r (A : type) : (xs : list A) → path _ (append A xs nil) xs =
  elim [
  | nil → refl
  | cons x (xs → ih) → λ i → cons x (ih i)
  ]

let append/ass (A : type)
  : (xs ys zs : list A)
  → path _ (append A xs (append A ys zs)) (append A (append A xs ys) zs)
  =
  elim [
  | nil → refl
  | cons x (xs → xs/ih) →
    λ ys zs i → cons x (xs/ih ys zs i)
  ]

-- encode-decode

let list/code (A : type) : list A → list A → type =
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

let list/refl (A : type) : (xs : list A) → list/code A xs xs =
  elim [
  | nil → triv
  | cons x (xs → refl/xs) → (refl, refl/xs)
  ]

let list/encode (A : type) (xs ys : list A) (q : path (list A) xs ys) : list/code A xs ys =
  coe 0 1 (list/refl A xs) in λ i → list/code A xs (q i)

let list/encode/refl (A : type) (xs : list A)
  : path (list/code A xs xs) (list/encode A xs xs refl) (list/refl A xs)
  =
  λ i → coe i 1 (list/refl A xs) in λ i → list/code A xs xs

let list/decode (A : type) : (xs ys : list A) → list/code A xs ys → path (list A) xs ys =
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

let list/decode/refl (A : type)
  : (xs : list A) → path (path (list A) xs xs) (list/decode A xs xs (list/refl A xs)) refl
  =
  elim [
  | nil → refl
  | cons x (xs → decode/refl/xs) → λ i j → cons x (decode/refl/xs i j)
  ]

let list/decode-encode/refl (A : type) (xs : list A)
  : path (path (list A) xs xs) (list/decode A xs xs (list/encode A xs xs refl)) refl
  =
  trans (path (list A) xs xs)
    (λ i → list/decode A xs xs (list/encode/refl A xs i))
    (list/decode/refl A xs)

let list/decode-encode (A : type) (xs ys : list A) (q : path (list A) xs ys)
  : path (path (list A) xs ys) (list/decode A xs ys (list/encode A xs ys q)) q
  =
  J (list A) xs
    (λ ys q → path (path (list A) xs ys) (list/decode A xs ys (list/encode A xs ys q)) q)
    (list/decode-encode/refl A xs)
    ys q

let list/encode/cons (A : type) (x y : A) (p : path A x y) (xs ys : list A) (q : path (list A) xs ys)
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

let list/encode-decode (A : type)
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

-- TODO: Can someone please prove that 'list' preserves hlevel?
