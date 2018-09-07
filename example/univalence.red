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
  ( g (c.fst),
    λ a i →
      comp 0 1 (g (c.snd (f a) i)) [
      | i=0 → h a
      | i=1 → refl
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
        | i=0 → p.snd
        | i=1 → refl
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
    | j=0 → A/prop a a
    | j=1 → A/prop a b
    | i=0 → A/prop a (p j)
    | i=1 → A/prop a (q j)
    ]

let LemSig
  (A : type) (B : A → type)
  (B/prop : (a : A) → IsProp (B a))
  (u v : (a : A) × B a)
  (P : Path A (u.fst) (v.fst))
  : Path ((a : A) × B a) u v
  =
  λ i →
    ( P i
    , PropToPropOver (λ i → B (P i)) (B/prop (P 1)) (u.snd) (v.snd) i
    )

let PropSig
  (A : type) (B : A → type)
  (A/prop : IsProp A)
  (B/prop : (a : A) → IsProp (B a))
  : IsProp ((a : A) × B a)
  =
  λ u v →
    LemSig A B B/prop u v (A/prop (u.fst) (v.fst))

opaque
let PropIsContr (A : type) : IsProp (IsContr A) =
  λ contr →
    let A/prop : IsProp A =
      λ a b i →
        comp 1 0 (contr.snd a i) [
        | i=0 → refl
        | i=1 → contr.snd b
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
    let a : A = ise y .fst .fst in
    let p : Path B (f a) y = ise y .fst .snd in
    let c : (w : Fiber A B f y) → Path (Fiber A B f y) w (a,p) =
      ise y .snd
    in
    let a' : A = ise' y .fst .fst in
    let p' : Path B (f a') y = ise' y .fst .snd in
    let c' : (w : Fiber A B f y) → Path (Fiber A B f y) w (a',p') =
      ise' y .snd
    in
    ( c' (a , p) i
    , λ w →
        let cap : (i j : dim) → Fiber A B f y =
          λ i j →
            comp 1 i (c' w j) [
            | j=0 → refl
            | j=1 → c' w
            ]
        in
        let face/i0 : (j k : dim) → Fiber A B f y =
          λ j k →
            comp 0 j w [
            | k=0 → cap 0
            | k=1 → c w
            ]
        in
        let sq : PathD (λ i → Path (Fiber A B f y) w (c' (a,p) i)) (c w) (c' w) =
          λ i j →
            comp 0 1 (cap i j) [
            | i=0 → face/i0 j
            | i=1 _ → c' w j
            | j=0 _ → w
            | j=1 k → c' (face/i0 1 k) i
            ]
        in
        sq i
    )

opaque
let EquivLemma
  (A B : type) (E0 E1 : Equiv A B)
  (P : Path (A → B) (E0.fst) (E1.fst))
  : Path (Equiv A B) E0 E1
  =
  LemSig (A → B) (IsEquiv A B) (PropIsEquiv A B) E0 E1 P


; per Dan Licata, UA and UABeta suffice for full univalence:
; https://groups.google.com/forum/#!topic/homotopytypetheory/j2KBIvDw53s

let UA/beta
  (A B : type) (E : Equiv A B) (a : A)
  : Path _ (coe 0 1 a in UA _ _ E) (E.fst a)
  =
  λ i →
    coe i 1 (E.fst a) in refl

let SigEquivToPath
  (A : type)
  (X : (B : type) × Equiv A B)
  : (B : type) × Path^1 type A B
  =
  ( X.fst
  , UA _ (X.fst) (X.snd)
  )

let SigPathToEquiv
  (A : type)
  (X : (B : type) × Path^1 type A B)
  : (B : type) × (Equiv A B)
  =
  ( X.fst
  , PathToEquiv _ (X.fst) (X.snd)
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
    ( singl.fst
    , UA/retract A (singl.fst) (singl.snd) i
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

let IdEquiv/weak-connection (B : type) : Equiv B B =
  ( λ b → b
  , λ b →
    ( (b, refl)
    , λ v i → (v.snd i, λ j → weak-connection/or B (v.snd) i j)
    )
  )

let univalence/alt (B : type) : IsContr^1 ((A : type) × Equiv A B) =
  ( (B, IdEquiv/weak-connection B)
  , λ w i →
      let VB : type = `(V i (fst w) B (snd w)) in
      let proj/B : VB → B = λ g → `(vproj i g (fst (snd w))) in
      ( _
      , proj/B
      , λ b →
           let ctr/B : dim → B =
             λ j →
               comp 1 j b [
               | i=0 → w.snd.snd b .fst .snd
               | i=1 → refl
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
