import prelude
import basics.retract
import paths.sigma
import paths.equivalence

-- the code in this file is adapted from yacctt and redprl

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

def univalence/alt (A : type) : is-contr^1 ((B : type) × equiv A B) =
  retract/hlevel^1 contr
    ((B : type) × equiv A B)
    ((B : type) × path^1 type A B)
    (ua/retract/sig A)
    (path/based/contr^1 type A)
