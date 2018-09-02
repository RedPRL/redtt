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
  (x y : A) → dec (Path A x y)

let dec/to/stable (A : type) (d : dec A) : stable A =
  or/elim A (neg A) (stable A) d
    (λ a _ → a)
    (λ x y → elim (y x) [])

let neg/is-prop-over (A : dim → type)
  : IsPropOver (λ i → neg (A i))
  =
  λ c c' i a →
   let f : [j] (A j → void) [ j=0 → c | j=1 → c' ] =
     elim (c (coe i 0 a in A)) []
   in
   f i a

; Hedberg's theorem for stable path types
let paths-stable/to/set (A : type)
  (st : (x y : A) → stable (Path A x y))
  : IsSet A
  =
  λ a b p q i j →
    let square : dim → dim → A =
      λ k m →
        comp 0 k a [
        | m=0 → p
        | m=1 → q
        ]
    in
    let cap : dim → dim → A =
      λ k m → st (p k) (q k) (λ c → c (square k)) m
    in
    comp 0 1 (cap j i) [
    | i=0 → λ k →
      st (p j) (p j)
         (neg/is-prop-over (λ j → neg (Path A (p j) (p j)))
           (λ c → c (square 0))
           (λ c → c (square 1))
           j)
         k
    | i=1 → refl
    | j=0 → λ k → weak-connection/or A (cap 0) i k
    | j=1 → λ k → weak-connection/or A (cap 1) i k
    ]

; Hedberg's theorem for decidable path types
let discrete/to/set (A : type) (d : discrete A)
  : IsSet A
  =
  paths-stable/to/set A (λ x y → dec/to/stable (Path A x y) (d x y))
