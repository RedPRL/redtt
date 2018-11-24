import prelude
import data.unit
import basics.isotoequiv
import paths.sigma
import paths.pi

def prop/unit (A : type) (A/prop : is-prop A) (x0 : A) : equiv A unit = 
  iso→equiv A unit (λ _ → ★, λ _ → x0, unit/prop ★, A/prop x0)

def prop/equiv (P Q : type) (P/prop : is-prop P) (Q/prop : is-prop Q) (f : P → Q) (g : Q → P) : equiv P Q = 
  iso→equiv P Q (f, g, λ p → Q/prop (f (g p)) p, λ q → P/prop (g (f q)) q)

def contr-equiv (A B : type) (A/contr : is-contr A) (B/contr : is-contr B)
  : equiv A B
  =
  ( λ _ → B/contr .fst
  , λ b →
    ( (A/contr .fst, symm B (B/contr .snd b))
    , λ (a,p) i →
      ( A/contr .snd a i
      , raise-hlevel prop B (raise-hlevel contr B B/contr)
        (B/contr .fst) b p (symm B (B/contr .snd b)) i
      )
    )
  )

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
