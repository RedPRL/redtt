import path
import hlevel
import equivalence
import connection
import retract

-- the code in this file is adapted from yacctt and redprl

def path→equiv (A B : type) (P : path^1 type A B) : equiv A B =
  coe 0 1 (id-equiv A) in λ i → equiv A (P i)

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

def ua/retract (A B : type) : retract^1 (equiv A B) (path^1 type A B) =
  ( ua A B
  , path→equiv A B
  , λ E →
    subtype/path _ (is-equiv _ _ ) (is-equiv/prop _ _) (path→equiv _ _ (ua A B E)) E
      (λ i a → ua/beta A B E (coe 1 i a in λ _ → A) i)
  )

def ua/retract/sig (A : type) : retract^1 ((B : type) × equiv A B) ((B : type) × path^1 type A B) =
  ( equiv→path/based A
  , path→equiv/based A
  , λ singl i →
    ( singl.fst
    , ua/retract A (singl.fst) .snd .snd (singl.snd) i
    )
  )

def ua/id-equiv (A : type) : path^1 _ (ua _ _ (id-equiv A)) refl =
  trans^1 _
    (λ i → ua A A (coe 0 i (id-equiv A) in λ _ → equiv A A))
    (path-retract/preserves-refl^1 _ equiv ua/retract A)

-- The following is a formulation of univalence proposed by Martin Escardo:
-- https://groups.google.com/forum/#!msg/homotopytypetheory/HfCB_b-PNEU/Ibb48LvUMeUJ
-- See also Theorem 5.8.4 of the HoTT Book.

def univalence (A : type) : is-contr^1 ((B : type) × equiv A B) =
  retract/hlevel^1 contr
    ((B : type) × equiv A B)
    ((B : type) × path^1 type A B)
    (ua/retract/sig A)
    (path/based/contr^1 type A)

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
