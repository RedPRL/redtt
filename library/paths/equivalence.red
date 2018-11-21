import prelude
import paths.sigma
import paths.pi
import paths.hlevel

-- hlevels of is-equiv and equiv

opaque
def is-equiv/prop (A B : type) (f : A → B) : is-prop (is-equiv A B f) =
  λ e0 e1 i b → is-contr/prop (fiber A B f b) (e0 b) (e1 b) i

-- A direct proof that is-equiv f is a prop, ported from cubicaltt to yacctt to redtt
def is-equiv/prop/direct (A B : type) (f : A → B) : is-prop (is-equiv _ _ f) =
  λ ise ise' i y →
    let ((a, p), c) = ise y in
    let ((a', p'), c') = ise' y in

    ( c' (a , p) i
    , λ w →
      let mycap (j k : 𝕀) : fiber A B f y =
        comp 1 j (c' w k) [
        | k=0 → refl
        | k=1 → c' w
        ]
      in
      let face/i0 (j k : 𝕀) : fiber A B f y =
        comp 0 j w [
        | k=0 → mycap 0
        | k=1 → c w
        ]
      in
      λ j →
      comp 0 1 (mycap i j) [
      | i=0 → face/i0 j
      | i=1 | j=0 → refl
      | j=1 k → c' (face/i0 1 k) i
      ]
    )

def equiv/level : (l : hlevel) (A B : type)
  (A/level : has-hlevel l A) (B/level : has-hlevel l B)
  → has-hlevel l (equiv A B)
  =
  elim [
  | contr → λ A B A/contr B/contr →
    ( contr-equiv A B A/contr B/contr
    , λ e i →
      ( λ a → B/contr .snd (e .fst a) i
      , prop→prop-over (λ j → is-equiv A B (λ a → B/contr .snd (e .fst a) j))
          (is-equiv/prop/direct A B (λ _ → B/contr .fst))
          (e .snd) (contr-equiv A B A/contr B/contr .snd)
          i
      )
    )
  | hsuc l → λ A B A/level B/level →
    sigma/hlevel (hsuc l) (A → B) (λ f → is-equiv _ _ f)
      (pi/hlevel (hsuc l) A (λ _ → B) (λ _ → B/level))
      (λ f → prop→hlevel l (is-equiv _ _ f) (is-equiv/prop/direct A B f))
  ]
