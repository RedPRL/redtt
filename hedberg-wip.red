import bool

;; WIP

data void where

let sg/elim
  (A : type) (B : A → type) (C : (x : A) (y : B x) → type)
  (t : (x : A) × B x)
  (m : (x : A) (y : B x) → C x y)
  : C (t.0) (t.1)
  =
  m (t.0) (t.1)

; Needed until we have parameterized datatypes
let or (A, B : type) : type =
  (b : bool) × elim b [tt ⇒ A | ff ⇒ B]

let or/elim
  (A, B : type)
  (C : type)
  (t : or A B)
  (m0 : A → C)
  (m1 : B → C)
  : C =
  sg/elim bool _ (λ _ _ → C) t
    (λ b →
      elim b [tt ⇒ m0 | ff ⇒ m1])

let neg (A : type) : type =
  A → void

let stable (A : type) : type =
  (neg (neg A)) → A

let dec (A : type) : type =
  or A (neg A)

let dec/stable (A : type) (d : dec A) : stable A =
  or/elim A (neg A) (stable A) d
    (λ a _ → a)
    (λ x y → elim (y x) [])
