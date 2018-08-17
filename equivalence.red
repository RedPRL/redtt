import path

let IsProp (C : type) : type =
  (c, c' : _)
  → Path C c c'

let IsContr (C : type) : type =
  (c : _) × (c' : _) → Path C c' c

let Fiber (A, B : type) (f : A → B) (b : B) : type =
  (a : _) × Path _ (f a) b

let IsEquiv (A, B : type) (f : A → B) : type =
  (b : B) → IsContr (Fiber _ _ f b)

let Equiv (A, B : type) : type =
  (f : A → B) × IsEquiv _ _ f

let UA (A,B : type) (E : Equiv A B) : Path^1 type A B =
  λ i →
    `(V i A B E)

