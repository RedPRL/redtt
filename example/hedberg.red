import void
import bool
import or
import connection
import ntype

let stable (A : type) : type =
  neg (neg A) → A

let dec (A : type) : type =
  or A (neg A)

let discrete (A : type) : type =
  (x y : A) → dec (path A x y)

let dec→stable (A : type) : dec A → stable A =
  elim [
  | inl a → λ _ → a
  | inr f → λ g → elim (g f) []
  ]

let neg/is-prop-over (A : dim → type)
  : is-prop-over (λ i → neg (A i))
  =
  λ c c' i a →
   let f : [j] (A j → void) [ j=0 → c | j=1 → c' ] =
     elim (c (coe i 0 a in A)) []
   in
   f i a


-- Hedberg's theorem for stable path types
let paths-stable→set (A : type)
  (st : (x y : A) → stable (path A x y))
  : is-set A
  =
  λ a b p q i j →
    let square (k m : dim) : A =
      comp 0 k a [
      | m=0 → p
      | m=1 → q
      ]
    in
    let cap (k m : dim) = st (p k) (q k) (λ c → c (square k)) m in
    comp 0 1 (cap j i) [
    | i=0 k →
      st (p j) (p j)
         (neg/is-prop-over (λ j → neg (path A (p j) (p j)))
           (λ c → c (square 0))
           (λ c → c (square 1))
           j)
         k
    | i=1 → refl
    | ∂[j] k → weak-connection/or A (cap j) i k
    ]

-- Hedberg's theorem for decidable path types
let discrete→set (A : type) (d : discrete A)
  : is-set A
  =
  paths-stable→set A (λ x y → dec→stable (path A x y) (d x y))
