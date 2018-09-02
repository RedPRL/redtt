import path
import ntype

let Fiber (A B : type) (f : A → B) (b : B) : type =
  (a : _) × Path _ (f a) b

let IsEquiv (A B : type) (f : A → B) : type =
  (b : B) → IsContr (Fiber _ _ f b)

let Equiv (A B : type) : type =
  (f : A → B) × IsEquiv _ _ f

let UA (A B : type) (E : Equiv A B) : Path^1 type A B =
  λ i →
    `(V i A B E)

let UAproj (A B : type) (E : Equiv A B)
  : PathD (λ i → `(V i A B E) → B) (λ a → E.0 a) (λ b → b)
  =
  λ i u →
    `(vproj i u A B (fst E))
