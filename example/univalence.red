import path
import ntype
import equivalence
import connection
import retract

; the code in this file is adapted from yacctt and redprl

let RetIsContr
  (A B : type)
  (f : A → B)
  (g : B → A)
  (h : Retract A B f g)
  (c : IsContr B)
  : IsContr A
  =
  ( g c.0,
    λ a i →
      comp 0 1 (g (c.1 (f a) i)) [
      | i=0 ⇒ h a
      | i=1 ⇒ refl
      ]
  )

let IdEquiv (A : type) : Equiv A A =
  ( λ a → a
  , λ a →
    ( (a, refl)
    , λ p i →
      let aux : dim → A =
        λ j →
        comp 1 j a [
        | i=0 ⇒ p.1
        | i=1 ⇒ refl
        ]
      in
      (aux 0, aux)
    )
  )

let PathToEquiv
  (A B : type) (P : Path^1 type A B)
  : Equiv A B
  =
  coe 0 1 (IdEquiv A) in λ i → Equiv A (P i)

let PropPi
  (A : type) (B : A → type)
  (B/prop : (a : A) → IsProp (B a))
  : IsProp ((a : A) → B a)
  =
  λ f g i a →
    B/prop a (f a) (g a) i

let PropSet
  (A : type) (A/prop : IsProp A)
  : (IsSet A)
  =
  λ a b p q i j →
    comp 0 1 a [
    | j=0 ⇒ A/prop a a
    | j=1 ⇒ A/prop a b
    | i=0 ⇒ A/prop a (p j)
    | i=1 ⇒ A/prop a (q j)
    ]

let LemSig
  (A : type) (B : A → type)
  (B/prop : (a : A) → IsProp (B a))
  (u v : (a : A) × B a)
  (P : Path A u.0 v.0)
  : Path ((a : A) × B a) u v
  =
  λ i →
    ( P i
    , let coe0 = coe 0 i u.1 in λ j → B (P j) in
      let coe1 = coe 1 i v.1 in λ j → B (P j) in
      B/prop (P i) coe0 coe1 i
    )


let PropSig
  (A : type) (B : A → type)
  (A/prop : IsProp A)
  (B/prop : (a : A) → IsProp (B a))
  : IsProp ((a : A) × B a)
  =
  λ u v →
    LemSig A B B/prop u v (A/prop u.0 v.0)

opaque
let PropIsContr (A : type) : IsProp (IsContr A) =
  λ contr →
    let A/prop : IsProp A =
      λ a b i →
        comp 1 0 (contr.1 a i) [
        | i=0 ⇒ refl
        | i=1 ⇒ contr.1 b
        ]
    in

    let contr/A/prop =
      PropSig _ (λ a → (b : A) → Path A b a) A/prop
        (λ a → PropPi A (λ b → Path A b a) (λ b → PropSet A A/prop b a))
    in

    contr/A/prop contr

opaque
let PropIsEquiv (A B : type) (f : A → B) : IsProp (IsEquiv A B f) =
  λ e0 e1 i b → PropIsContr (Fiber A B f b) (e0 b) (e1 b) i

; A direct proof that IsEquiv f is a prop, ported from cubicaltt to yacctt to redtt
let PropIsEquivDirect (A B : type) (f : A → B) : IsProp (IsEquiv A B f) =
  λ ise ise' i y →
    let a : A = (ise y).0.0 in
    let p : Path B (f a) y = (ise y).0.1 in
    let c : (w : Fiber A B f y) → Path (Fiber A B f y) w (a,p) =
      (ise y).1
    in
    let a' : A = (ise' y).0.0 in
    let p' : Path B (f a') y = (ise' y).0.1 in
    let c' : (w : Fiber A B f y) → Path (Fiber A B f y) w (a',p') =
      (ise' y).1
    in
    ( c' (a , p) i
    , λ w →
        let sq : PathD (λ j → Path (Fiber A B f y) w (c' (a,p) j)) (c w) (c' w) =
          λ i j →
            comp 0 1 (connection/and (Fiber A B f y) (c' w) i j) [
            | i=0 ⇒ λ k → connection/and (Fiber A B f y) (c w) k j
            | i=1 ⇒ λ _ → c' w j
            | j=0 ⇒ λ _ → w
            | j=1 ⇒ λ k → c' (c w k) i
            ]
        in
        sq i
    )

opaque
let EquivLemma
  (A B : type) (E0 E1 : Equiv A B)
  (P : Path (A → B) E0.0 E1.0)
  : Path (Equiv A B) E0 E1
  =
  LemSig (A → B) (IsEquiv A B) (PropIsEquiv A B) E0 E1 P


; per Dan Licata, UA and UABeta suffice for full univalence:
; https://groups.google.com/forum/#!topic/homotopytypetheory/j2KBIvDw53s

let UA/beta
  (A B : type) (E : Equiv A B) (a : A)
  : Path _ (coe 0 1 a in UA _ _ E) (E.0 a)
  =
  λ i →
    coe i 1 (E.0 a) in refl

let SigEquivToPath
  (A : type)
  (X : (B : type) × Equiv A B)
  : (B : type) × Path^1 type A B
  =
  ( X.0
  , UA _ X.0 X.1
  )

let SigPathToEquiv
  (A : type)
  (X : (B : type) × Path^1 type A B)
  : (B : type) × (Equiv A B)
  =
  ( X.0
  , PathToEquiv _ X.0 X.1
  )

opaque
let UA/retract
  (A B : type)
  : Retract^1 (Equiv A B) (Path^1 type A B) (UA A B) (PathToEquiv A B)
  =
  λ E →
    EquivLemma _ _ (PathToEquiv _ _ (UA A B E)) E
      (λ i a → UA/beta A B E (coe 1 i a in λ _ → A) i)

let UA/retract/sig
  (A : type)
  : Retract^1 _ _ (SigEquivToPath A) (SigPathToEquiv A)
  =
  λ singl i →
    ( singl.0
    , UA/retract A singl.0 singl.1 i
    )

let UA/IdEquiv (A : type)
  : Path^1 (Path^1 type A A) (UA A A (IdEquiv A)) (λ _ → A)
  =
  trans^1 (Path^1 type A A)
    (λ i → UA A A (coe 0 i (IdEquiv A) in λ _ → Equiv A A))
    (path-retract/preserves/refl^1
       type Equiv UA PathToEquiv UA/retract A)

opaque
let IsContrPath (A : type) : IsContr^1 ((B : _) × Path^1 type A B) =
  ( (_, λ _ → A)
  , λ X i →
    ( comp 0 1 A [
      | i=0 ⇒ X.1
      | i=1 ⇒ refl
      ]
    , λ j →
      comp 0 j A [
      | i=0 ⇒ X.1
      | i=1 ⇒ refl
      ]
    )
  )


; The following is a formulation of univalence proposed by Martin Esfstdo:
; https://groups.google.com/forum/#!msg/homotopytypetheory/HfCB_b-PNEU/Ibb48LvUMeUJ
; See also Theorem 5.8.4 of the HoTT Book.

let univalence (A : type) : IsContr^1 ((B : type) × Equiv A B) =
  RetIsContr^1
    _
    _
    (SigEquivToPath A)
    (SigPathToEquiv A)
    (UA/retract/sig A)
    (IsContrPath A)

let IdEquiv/connection (B : type) : Equiv B B =
  ( λ b → b
  , λ b →
    ( (b, refl)
    , λ v i → (v.1 i, λ j → connection/or B v.1 i j)
    )
  )

let univalence/alt (B : type) : IsContr^1 ((A : type) × Equiv A B) =
  ( (B, IdEquiv/connection B)
  , λ w i →
      let VB : type = `(V i (fst w) B (snd w)) in
      let proj/B : VB → B = λ g → `(vproj i g (fst w) B (snd w)) in
      ( _
      , proj/B
      , λ b →
           let ctr/B : dim → B =
             λ j →
               comp 1 j b [
               | i=0 ⇒ (w.1.1 b).0.1
               | i=1 ⇒ refl
               ]
           in
           let ctr : Fiber VB B proj/B b =
             ( `(vin i (fst (fst ((snd (snd w)) b))) (@ ctr/B 0)), ctr/B )
           in
           ( ctr
           , λ v j →
               let filler : dim → B =
                 λ l →
                   comp 1 l b [
                   | i=0 ⇒ ((w.1.1 b).1 v j).1
                   | i=1 ⇒ λ k → connection/or B v.1 j k
                   | j=0 ⇒ v.1
                   | j=1 ⇒ ctr/B
                   ]
               in
               ( `(vin i (fst (@ ((snd ((snd (snd w)) b)) v) j)) (@ filler 0))
               , filler
               )
           )
      )
  )
