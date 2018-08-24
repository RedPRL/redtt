import path
import connection

let Retract (A,B : type) (f : A → B) (g : B → A) : type =
  (a : A) →
    Path A (g (f a)) a

; Adapted from https://github.com/HoTT/book/issues/718
let path-retract/preserves/refl (A : type) (R : A → A → type)
  (s : (x,y : A) → (R x y) → Path A x y)
  (r : (x,y : A) → (Path A x y) → R x y)
  (α : (x,y : A) → Retract (R x y) (Path A x y) (s x y) (r x y))
  : (x : A) → Path (Path A x x) (s x x (r x x (λ _ → x))) (λ _ → x)
  =
  λ x →
  let q : Path A x x =
    s x x (r x x (λ _ → x))
  in
  let cap1 : [i j] A [
    | j=0 ⇒ x
    | j=1 ⇒ q i
    | i=0 ⇒ q j
    | i=1 ⇒ s x x (r x x q) j
    ]
    =
    λ i j →
      s x (q i) (r x (q i) (λ k → connection/and A q i k)) j
  in
  let cap2 : [i j] A [
    | j=0 ⇒ x
    | j=1 ⇒ q i
    | i=0 ⇒ q j
    | i=1 ⇒ q j
    ]
    =
    λ i j →
      comp 0 1 (cap1 i j) [
      | j=0 ⇒ refl
      | j=1 ⇒ refl
      | i=0 ⇒ refl
      | i=1 ⇒ λ k → s x x (α x x (r x x (λ _ → x)) k) j
      ]
  in
  let face : dim → dim → A
    =
    λ m k →
     comp 0 m x [
     | k=0 ⇒ q
     | k=1 ⇒ λ _ → x
     ]
  in
  λ i j →
    comp 0 1 (cap2 i j) [
    | j=0 ⇒ λ _ → x
    | j=1 ⇒ face i
    | i=0 ⇒ λ _ → q j
    | i=1 ⇒ face j
    ]
