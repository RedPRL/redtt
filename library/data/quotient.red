data (A : type) (R : A → A → type) ⊢ quotient where
| pt (a : A)
| gl (a b : A) (p : R a b) (i : 𝕀) [
  | i=0 → pt a
  | i=1 → pt b
  ]
