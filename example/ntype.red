import path

let is-contr (C : type) : type =
  (c : _) × (c' : _) → path C c' c

/-
let is-param-contr-over (A : type) (B : A → type) : type =
  (c : (a : _) → B a) × (a : dim → A) (c' : B (a 0)) → pathd (λ i → B (a i)) c' (c (a 1))
-/

let is-prop (C : type) : type =
  (c c' : _)
  → path C c c'

let is-prop-over (A : dim → type) : type =
  (a : A 0) → (b : A 1) → pathd A a b

let prop→prop-over (A : dim → type) (p : is-prop (A 1))
  : is-prop-over A
  =
  λ a b i →
    comp 0 1 (coe 0 i a in A) [
    | i=0 → refl
    | i=1 → p (coe 0 1 a in A) b
    ]

let is-set (C : type) : type =
  (c c' : C)
  → is-prop (path _ c c')
