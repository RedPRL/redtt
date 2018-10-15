import prelude.path
import prelude.connection
import prelude.hlevel

-- retracts

def is-section (A B : type) (f : A → B) : type =
  (g : B → A) × (a : A) → path A (g (f a)) a

def retract (A B : type) : type =
  (f : A → B) × is-section A B f

-- equivalences

def fiber (A B : type) (f : A → B) (b : B) : type =
  (a : _) × path _ (f a) b

def is-equiv (A B : type) (f : A → B) : type =
  (b : B) → is-contr (fiber _ _ f b)

def equiv (A B : type) : type =
  (f : A → B) × is-equiv _ _ f

-- identity equivalences

def id-equiv (A : type) : equiv A A =
  ( λ a → a
  , λ a →
    ( (a, refl)
    , λ p i →
      let aux (j : 𝕀) : A =
        comp 1 j a [
        | i=0 → p.snd
        | i=1 → refl
        ]
      in
      (aux 0, aux)
    )
  )

def id-equiv/weak-connection (B : type) : equiv B B =
  ( λ b → b
  , λ b →
    ( (b, refl)
    , λ v i → (v.snd i, λ j → weak-connection/or B (v.snd) i j)
    )
  )


