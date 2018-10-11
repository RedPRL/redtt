import path
import hlevel
import retract
import equivalence
import isotoequiv

def pi/path (A : type) (B : A → type) (f f' : (a : A) → B a)
  : equiv ((a : A) → path (B a) (f a) (f' a)) (path ((a : A) → B a) f f')
  =
  iso→equiv
    ((a : A) → path (B a) (f a) (f' a))
    (path ((a : A) → B a) f f')
    ( λ g i a → g a i
    , λ p a i → p i a
    , λ _ → refl
    , λ _ → refl
    )

def pi/level : (l : hlevel) (A : type) (B : A → type)
  (B/level : (a : A) → has-hlevel l (B a))
  → has-hlevel l ((a : A) → B a)
  =
  elim [
  | contr → λ A B B/contr → (λ a → B/contr a .fst, λ f i a → B/contr a .snd (f a) i)
  | hsuc l →
    elim l [
    | contr → λ A B B/prop f f' i a → B/prop a (f a) (f' a) i
    | hsuc (l → l/ih) → λ A B B/level f f' →
      retract/hlevel (hsuc l)
        (path ((a : A) → B a) f f')
        ((a : A) → path (B a) (f a) (f' a))
        (λ p a i → p i a)
        (λ g i a → g a i)
        (λ _ → refl)
        (l/ih A (λ a → path (B a) (f a) (f' a)) (λ a → B/level a (f a) (f' a)))
    ]
  ]
