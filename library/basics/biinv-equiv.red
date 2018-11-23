import prelude
import basics.isotoequiv
import basics.retract

-- Bi-invertible map definition of equivalence

def is-biinv-equiv (A B : type) (f : A → B) : type =
  section A B f × retraction A B f

def biinv-equiv (A B : type) : type = (f : A → B) × is-biinv-equiv A B f

def biinv-equiv→iso (A B : type) : biinv-equiv A B → iso A B =
  λ (f,(g,α),h,β) →
  let β' (a : A) : path _ (g (f a)) a =
    λ i →
    comp 0 1 (h (α (f a) i)) [
    | i=0 j → β (g (f a)) j
    | i=1 j → β a j
    ]
  in
  (f,g,α,β')
