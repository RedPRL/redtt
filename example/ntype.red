import path

let IsContr (C : type) : type =
  (c : _) × (c' : _) → Path C c' c

let IsProp (C : type) : type =
  (c, c' : _)
  → Path C c c'

let IsPropOver (A : dim → type) : type =
  (a : A 0) → (b : A 1) → PathD A a b

let PropToPropOver (A : dim → type) (p : IsProp (A 1))
  : IsPropOver A
  =
  λ a b i →
    comp 0 1 (coe 0 i a in A) [
    | i=0 ⇒ refl
    | i=1 ⇒ p (coe 0 1 a in A) b
    ]

let IsSet (C : type) : type =
  (c, c' : _)
  → IsProp (Path C c c')
