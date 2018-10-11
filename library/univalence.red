import path
import hlevel
import equivalence
import connection
import retract

-- the code in this file is adapted from yacctt and redprl

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

def path→equiv (A B : type) (P : path^1 type A B) : equiv A B =
  coe 0 1 (id-equiv A) in λ i → equiv A (P i)

def pi/prop (A : type) (B : A → type) (B/prop : (a : A) → is-prop (B a)) : is-prop ((a : A) → B a) =
  λ f g i a →
  B/prop a (f a) (g a) i

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

def subtype-of-prop/prop
  (A : type) (B : A → type)
  (A/prop : is-prop A)
  (B/prop : (a : A) → is-prop (B a))
  : is-prop ((a : A) × B a)
  =
  λ u v →
  subtype/path A B B/prop u v (A/prop (u.fst) (v.fst))

opaque
def is-contr/prop (A : type) : is-prop (is-contr A) =
  λ contr →
    let A/prop : is-prop A =
      λ a b i →
      comp 1 0 (contr.snd a i) [
      | i=0 → refl
      | i=1 → contr.snd b
      ]
    in
    subtype-of-prop/prop _ (λ a → (b : A) → path A b a) A/prop
      (λ a → pi/prop A (λ b → path A b a) (λ b → prop→set _ A/prop b a))
      contr

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


-- per Dan Licata, ua and ua/beta suffice for full univalence:
-- https://groups.google.com/forum/#!topic/homotopytypetheory/j2KBIvDw53s

def ua/beta (A B : type) (E : equiv A B) (a : A) : path _ (coe 0 1 a in ua _ _ E) (E.fst a) =
  λ i → coe i 1 (E.fst a) in refl

def equiv→path/based (A : type) (X : (B : type) × equiv A B) : (B : type) × path^1 type A B =
  ( X.fst
  , ua _ (X.fst) (X.snd)
  )

def path→equiv/based (A : type) (X : (B : type) × path^1 type A B) : (B : type) × equiv A B =
  ( X.fst
  , path→equiv _ (X.fst) (X.snd)
  )

opaque
def ua/retract (A B : type) : retract^1 _ _ (ua A B) (path→equiv A B) =
  λ E →
    subtype/path _ (is-equiv _ _ ) (is-equiv/prop _ _) (path→equiv _ _ (ua A B E)) E
      (λ i a → ua/beta A B E (coe 1 i a in λ _ → A) i)

def ua/retract/sig (A : type) : retract^1 _ _ (equiv→path/based A) (path→equiv/based A) =
  λ singl i →
    ( singl.fst
    , ua/retract _ (singl.fst) (singl.snd) i
    )

def ua/id-equiv (A : type) : path^1 _ (ua _ _ (id-equiv A)) refl =
  trans^1 _
    (λ i → ua A A (coe 0 i (id-equiv A) in λ _ → equiv A A))
    (path-retract/preserves/refl^1 _ _ ua path→equiv ua/retract A)

opaque
def path/based/contr (A : type) : is-contr^1 ((B : _) × path^1 _ A B) =
  ( (A, refl)
  , λ X i →
    ( comp 0 1 A [
      | i=0 → X.snd
      | i=1 → refl
      ]
    , λ j →
      comp 0 j A [
      | i=0 → X.snd
      | i=1 → refl
      ]
    )
  )


-- The following is a formulation of univalence proposed by Martin Escardo:
-- https://groups.google.com/forum/#!msg/homotopytypetheory/HfCB_b-PNEU/Ibb48LvUMeUJ
-- See also Theorem 5.8.4 of the HoTT Book.

def univalence (A : type) : is-contr^1 ((B : type) × equiv A B) =
  retract/hlevel^1 contr
    _
    _
    (equiv→path/based A)
    (path→equiv/based A)
    (ua/retract/sig A)
    (path/based/contr A)

def id-equiv/weak-connection (B : type) : equiv B B =
  ( λ b → b
  , λ b →
    ( (b, refl)
    , λ v i → (v.snd i, λ j → weak-connection/or B (v.snd) i j)
    )
  )

def univalence/alt (B : type) : is-contr^1 ((A : type) × equiv A B) =
  ( (B, id-equiv/weak-connection B)
  , λ w i →
      let VB : type = `(V i (fst w) B (snd w)) in
      let proj/B (g : VB) : B = `(vproj i g (fst (snd w))) in
      ( _
      , proj/B
      , λ b →
        let ctr/B (j : 𝕀) : B =
          comp 1 j b [
          | i=0 → w.snd.snd b .fst .snd
          | i=1 → refl
          ]
        in
        let ctr : fiber VB B proj/B b =
          (`(vin i (fst (fst ((snd (snd w)) b))) (@ ctr/B 0)), ctr/B)
        in
        ( ctr
        , λ v j →
          let filler (l : 𝕀) : B =
            comp 1 l b [
            | i=0 → w.snd.snd b .snd v j .snd
            | i=1 k → weak-connection/or B (v.snd) j k
            | j=0 → v.snd
            | j=1 → ctr/B
            ]
          in
          ( `(vin i (fst (@ ((snd ((snd (snd w)) b)) v) j)) (@ filler 0))
          , filler
          )
        )
      )
  )
