import prelude
import basics.isotoequiv
import basics.retract

-- Bi-invertible map definition of equivalence

def is-biinv-equiv (A B : type) (f : A → B) : type =
  section A B f × retraction A B f

def biinv-equiv (A B : type) : type = (f : A → B) × is-biinv-equiv A B f

def biinv-equiv→iso (A B : type) (bie : biinv-equiv A B) : iso A B =
  let (f,(g,α),(h,β)) = bie in
  let β' (a : A) : path _ (g (f a)) a =
    λ i →
    comp 0 1 (h (α (f a) i)) [
    | i=0 j → β (g (f a)) j
    | i=1 j → β a j
    ]
  in
  (f,g,α,β')

def biinv-equiv/prop (A B : type) (f : A → B) : is-prop (is-biinv-equiv A B f) =
  λ (s0,r0) (s1,r1) i →
  let c = iso→equiv _ _ (biinv-equiv→iso _ _ (f,s0,r0)) .snd in
  (equiv-section/prop A B f c s0 s1 i, equiv-retraction/prop A B f c r0 r1 i)
