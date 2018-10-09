import path
import ntype

def fiber (A B : type) (f : A → B) (b : B) : type =
  (a : _) × path _ (f a) b

def is-equiv (A B : type) (f : A → B) : type =
  (b : B) → is-contr (fiber _ _ f b)

/-
def is-equiv-over (A B : type) (f : A → B) : type =
  is-param-contr-over _ (fiber _ _ f)
-/

def equiv (A B : type) : type =
  (f : A → B) × is-equiv _ _ f

/-
def equiv-over (A B : type) : type =
  (f : A → B) × is-equiv-over _ _ f
-/

def ua (A B : type) (E : equiv A B) : path^1 type A B =
  λ i →
    `(V i A B E)

def ua/proj (A B : type) (E : equiv A B)
  : pathd (λ i → `(V i A B E) → B) (λ a → E.fst a) (λ b → b)
  =
  λ i u →
    `(vproj i u (fst E))
