import prelude
import basics.isotoequiv
import data.truncation
import paths.hlevel

def prop/trunc (A : type) (A/prop : is-prop A) : equiv A (trunc A) = 
  prop/equiv _ _ A/prop (trunc/prop A) 
    (λ x → ret x) (elim [ ret a → a | glue (x → x/ih) (y → y/ih) i → A/prop x/ih y/ih i ])

def unique-choice (A : type) (P : A → type) 
  (P/prop : (x : A) → is-prop (P x)) (P/trunc : (x : A) → trunc (P x)) 
  : (x : A) → P x 
  =
  λ x → coe 0 1 (P/trunc x) in symm^1 _ (ua _ _ (prop/trunc (P x) (P/prop x)))
