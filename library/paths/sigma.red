import prelude
import basics.isotoequiv
import basics.retract

def sigma/assoc (A : type) (B : A → type) (C : ((x : A) × B x) → type) 
  : equiv ((x : A) × (y : B x) × C (x, y)) ((p : ((x : A) × B x)) × C p) 
  = 
  ( λ x → ((x.fst, x.snd.fst), x.snd.snd)
  , λ b → ( ((b.fst.fst, b.fst.snd, b.snd), refl)
          , λ c i → 
            ( ((c.snd i).fst.fst, (c.snd i).fst.snd, (c.snd i).snd)
            , λ j → weak-connection/or _ (c.snd) i j
            )
          )
  )

def sigma/contr/equiv/fst (A : type) (P : A → type) (P/contr : (x : A) → is-contr (P x)) 
  : equiv ((x : A) × P x) A 
  = 
  iso→equiv ((x : A) × P x) A 
    ( λ s → s.fst
    , λ x → (x, (P/contr x).fst)
    , refl
    , λ s i → (s.fst, symm _ ((P/contr (s.fst)).snd (s.snd)) i)
    )  

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
      retract/hlevel (hsuc l)
        (path ((a : A) × B a) (a,b) (a',b'))
        ((p : path A a a') × pathd (λ i → B (p i)) b b')
        ( λ r → (λ i → r i .fst, λ i → r i .snd)
        , λ (p,q) i → (p i, q i)
        , λ _ → refl
        )
        (l/ih (path A a a') (λ p → pathd (λ i → B (p i)) b b')
          (A/level a a') (λ p → pathd/hlevel (hsuc l) A B p (B/level a') b b'))
    ]
  ]

def subtype/path
  (A : type) (B : A → type)
  (B/prop : (a : A) → is-prop (B a))
  (u v : (a : A) × B a)
  (P : path A (u.fst) (v.fst))
  : path ((a : A) × B a) u v
  =
  λ i →
  ( P i
  , prop→prop-over (λ i → B (P i)) (B/prop (P 1)) (u.snd) (v.snd) i
)