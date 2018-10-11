import hlevel
import equivalence
import isotoequiv

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

def sigma/hlevel : (l : hlevel) (A : type) (B : A → type)
  (A/level : has-hlevel l A) (B/level : (a : A) → has-hlevel l (B a))
  → has-hlevel l ((a : A) × B a)
  =
  elim [
  | contr → λ A B A/contr B/contr →
    ( (A/contr .fst, B/contr (A/contr .fst) .fst)
    , λ (a,b) i →
      ( A/contr .snd a i
      , B/contr (A/contr .snd a i) .snd
         (coe 0 i b in λ j → B (A/contr .snd a j))
         i
      )
    )
  | hsuc l →
    elim l [
    | contr → λ A B A/prop B/prop (a,b) (a',b') i →
      let A/path = A/prop a a' in
      (A/path i, prop→prop-over (λ j → B (A/path j)) (B/prop a') b b' i)
    | hsuc (l → l/ih) → λ A B A/level B/level (a,b) (a',b') →
      hlevel/transport (hsuc l)
        ((p : path A a a') × pathd (λ i → B (p i)) b b')
        (path ((a : A) × B a) (a,b) (a',b')) 
        (sigma/path A B a b a' b')
        (l/ih (path A a a') (λ p → pathd (λ i → B (p i)) b b')
          (A/level a a') (λ p → pathd/hlevel (hsuc l) A B p (B/level a') b b'))
    ]
  ]
