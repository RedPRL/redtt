import path
import hlevel
import sigma
import pi

def fiber (A B : type) (f : A → B) (b : B) : type =
  (a : _) × path _ (f a) b

def is-equiv (A B : type) (f : A → B) : type =
  (b : B) → is-contr (fiber _ _ f b)

/-
def is-equiv-over (A B : type) (f : A → B) : type =
  is-param-contr-over _ (fiber _ _ f)
-/

def equiv (A B : type) : type =
  (f : A → B) × is-equiv _ _ f

/-
def equiv-over (A B : type) : type =
  (f : A → B) × is-equiv-over _ _ f
-/


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


-- V types

def ua (A B : type) (E : equiv A B) : path^1 type A B =
  λ i →
    `(V i A B E)

def ua/proj (A B : type) (E : equiv A B)
  : pathd (λ i → `(V i A B E) → B) (λ a → E.fst a) (λ b → b)
  =
  λ i u →
    `(vproj i u (fst E))


-- hlevels of is-equiv and equiv

opaque
def is-contr/prop (A : type) : is-prop (is-contr A) =
  λ A/contr →
    let A/prop : is-prop A = raise-hlevel contr A A/contr in
    sigma/hlevel prop _ (λ a → (b : A) → path A b a) A/prop
      (λ a → pi/hlevel prop A (λ b → path A b a) (λ b → prop→set _ A/prop b a))
      A/contr

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
      let cap (j k : 𝕀) : fiber A B f y =
        comp 1 j (c' w k) [
        | k=0 → refl
        | k=1 → c' w
        ]
      in
      let face/i0 (j k : 𝕀) : fiber A B f y =
        comp 0 j w [
        | k=0 → cap 0
        | k=1 → c w
        ]
      in
      λ j →
      comp 0 1 (cap i j) [
      | i=0 → face/i0 j
      | i=1 | j=0 → refl
      | j=1 k → c' (face/i0 1 k) i
      ]
    )

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

