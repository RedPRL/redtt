import path
import equivalence
import isotoequiv

-- characterize the path type for various type formers

def sigma/path (A : type) (B : A → type) (a : A) (b : B a) (a' : A) (b' : B a')
  : equiv ((p : path A a a') × pathd (λ i → B (p i)) b b') (path ((a : A) × B a) (a,b) (a',b')) 
  =
  iso→equiv
    ((p : path A a a') × pathd (λ i → B (p i)) b b')
    (path ((a : A) × B a) (a,b) (a',b'))
    ( λ (p,q) i → (p i, q i)
    , λ r → (λ i → r i .fst, λ i → r i .snd)
    , λ _ → refl
    , λ _ → refl
    )

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

