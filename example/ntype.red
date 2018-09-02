import path

let IsContr (C : type) : type =
  (c : _) × (c' : _) → Path C c' c

let IsProp (C : type) : type =
  (c c' : _)
  → Path C c c'

let IsPropOver (A : dim → type) : type =
  (a : A 0) → (b : A 1) → PathD A a b

let IsSet (C : type) : type =
  (c c' : _)
  → IsProp (Path C c c')
