import path

data trunc (A : type) where
| ret (a : A)
| glue (x y : trunc) (i : 𝕀) [
  | i=0 → x
  | i=1 → y
  ]

def trunc/bind (A B : type) (f : A → trunc B) (m : trunc A) : trunc B =
  elim m [
  | ret a → f a
  | glue (x → x/ih) (y → y/ih) i → glue x/ih y/ih i
  ]

def trunc/bind/ret (A : type) : path _ (trunc/bind A A (λ a → ret a)) (λ x → x) =
  funext _ _ (trunc/bind A A (λ a → ret a)) (λ x → x)
    (elim [
     | ret a → refl
     | glue (x → x/ih) (y → y/ih) i →
       λ j → glue (x/ih j) (y/ih j) i
     ])

