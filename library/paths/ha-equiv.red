import prelude
import basics.isotoequiv
import basics.retract
import basics.ha-equiv
import paths.pi

-- this is actually an equivalence, but we don't need that
def lcoh/retract-of-fiber-path (A B : type) (f : A → B) (c : is-equiv A B f)
  (g : B → A) (f-g : (b : _) → path _ (f (g b)) b)
  : retract
    (lcoh A B f g f-g)
    ((a : A) → path (fiber A B f (f a)) (g (f a), f-g (f a)) (a, refl))
  =
  ( λ (g-f,adj) a i →
    ( g-f a i
    , λ j →
      comp 1 0 (adj a j i) [
      | i=0 k → symm/filler B (λ n → f-g (f a) n) j k
      | i=1 | j=0 → refl
      | j=1 k → weak-connection/or-not B (λ v → f-g (f a) v) i k
      ]
    )
  , λ p →
    ( λ a i → p a i .fst
    , λ a j i →
      comp 0 1 (p a i .snd j) [
      | i=0 k → symm/filler B (λ n → f-g (f a) n) j k
      | i=1 | j=0 → refl
      | j=1 k → weak-connection/or-not B (λ v → f-g (f a) v) i k
      ]
    )
  , λ (g-f,adj) k →
    ( g-f
    , λ a j i →
      let capk : B =
        comp 1 k (adj a j i) [
        | i=0 k → symm/filler B (λ n → f-g (f a) n) j k
        | i=1 | j=0 → refl
        | j=1 k → weak-connection/or-not B (λ v → f-g (f a) v) i k
        ]
      in
      comp k 1 capk [
      | i=0 k → symm/filler B (λ n → f-g (f a) n) j k
      | i=1 | j=0 → refl
      | j=1 k → weak-connection/or-not B (λ v → f-g (f a) v) i k
      ]
    )
  )

def equiv-lcoh/prop (A B : type) (f : A → B) (c : is-equiv A B f)
  (g : B → A) (f-g : (b : _) → path _ (f (g b)) b)
  : is-prop (lcoh A B f g f-g)
  =
  retract/hlevel prop _ _
    (lcoh/retract-of-fiber-path A B f c g f-g)
    (pi/hlevel prop A _
      (λ a →
       prop→set (fiber A B f (f a))
         (contr→prop (fiber A B f (f a)) (c (f a)))
         (g (f a), f-g (f a)) (a, refl)))

def is-ha-equiv/prop (A B : type) (f : A → B) : is-prop (is-ha-equiv A B f) =
  λ (g0,f-g0,g0-f,adj0) (g1,f-g1,g1-f,adj1) i →
  let c = iso→equiv _ _ (f,g0,f-g0,g0-f) .snd in
  let p = equiv-section/prop A B f c (g0,f-g0) (g1,f-g1) in
  let q = prop→prop-over (λ i → lcoh A B f (p i .fst) (p i .snd))
           (equiv-lcoh/prop A B f c g1 f-g1) (g0-f,adj0) (g1-f,adj1)
  in
  (p i .fst, p i .snd, q i .fst, q i .snd)


