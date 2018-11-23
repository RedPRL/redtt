import prelude
import basics.isotoequiv
import basics.retract
import basics.biinv-equiv

def biinv-equiv/prop (A B : type) (f : A → B) : is-prop (is-biinv-equiv A B f) =
  λ (s0,r0) (s1,r1) i →
  let c = iso→equiv _ _ (biinv-equiv→iso _ _ (f,s0,r0)) .snd in
  (equiv-section/prop A B f c s0 s1 i, equiv-retraction/prop A B f c r0 r1 i)
