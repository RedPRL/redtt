import bool

-- Needed until we have parameterized datatypes
let or (A B : type) : type =
  (b : bool) × elim b [tt → A | ff → B]

let or/elim (A B : type) (C : type) : (t : or A B) (m0 : A → C) (m1 : B → C) → C =
  λ [,] →
  elim [
  | tt → λ x m0 _ → m0 x
  | ff → λ x _ m1 → m1 x
  ]
