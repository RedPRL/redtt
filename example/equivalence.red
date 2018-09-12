import path
import ntype

let fiber (A B : type) (f : A → B) (b : B) : type =
  (a : _) × path _ (f a) b

let is-equiv (A B : type) (f : A → B) : type =
  (b : B) → is-contr (fiber _ _ f b)

let equiv (A B : type) : type =
  (f : A → B) × is-equiv _ _ f

let ua (A B : type) (E : equiv A B) : path^1 type A B =
  λ i →
    `(V i A B E)

let ua/proj (A B : type) (E : equiv A B)
  : pathd (λ i → `(V i A B E) → B) (λ a → E.fst a) (λ b → b)
  =
  λ i u →
    `(vproj i u (fst E))
