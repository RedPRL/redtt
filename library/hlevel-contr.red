import path
import hlevel
import sigma
import pi

def is-contr/prop (A : type) : is-prop (is-contr A) =
  λ A/contr →
    let A/prop : is-prop A = raise-hlevel contr A A/contr in
    sigma/hlevel prop _ (λ a → (b : A) → path A b a) A/prop
      (λ a → pi/hlevel prop A (λ b → path A b a) (λ b → prop→set _ A/prop b a))
      A/contr

def has-hlevel/prop : (l : hlevel) (A : type) → is-prop (has-hlevel l A) =
  elim [
  | contr → is-contr/prop
  | hsuc l → elim l [
    | contr → λ A A/prop A/prop' i a a' →
      prop→set A A/prop a a' (A/prop a a') (A/prop' a a') i
    | hsuc (l → l/ih) → λ A A/level A/level' i a a' →
      l/ih (path A a a') (A/level a a') (A/level' a a') i
    ]
  ]
