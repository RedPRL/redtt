import path
import equivalence
import connection

; the code in this file is adapted from yacctt and redprl

let IsProp (C : type) : type =
  (c, c' : _) →
    Path C c c'

let IsSet (C : type) : type =
  (c, c' : _) →
    IsProp (Path C c c')


let Retract (A,B : type) (f : A → B) (g : B → A) : type =
  (a : A) →
    Path A (g (f a)) a

let RetIsContr
  (A,B : type)
  (f : A → B)
  (g : B → A)
  (h : Retract A B f g)
  (c : IsContr B)
  : IsContr A
  =
  < g (c.0),
    λ a i →
      comp 0 1 (g (c.1 (f a) i)) with
      | i=0 ⇒ h a
      | i=1 ⇒ λ _ → g (c.0)
      end
  >

let IdEquiv (A : type) : Equiv A A =
  < λ a → a
  , λ a →
    < <a, λ _ → a>
    , λ p i →
      let aux : dim → A =
        λ j →
        comp 1 j a with
        | i=0 ⇒ λ k → p.1 k
        | i=1 ⇒ λ _ → a
        end
      in
      <aux 0, λ j → aux j>
    >
  >

let PathToEquiv
  (A,B : type) (P : Path^1 type A B)
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
    comp 0 1 a with
    | j=0 ⇒ λ k → A/prop a a k
    | j=1 ⇒ λ k → A/prop a b k
    | i=0 ⇒ λ k → A/prop a (p j) k
    | i=1 ⇒ λ k → A/prop a (q j) k
    end

let LemSig
  (A : type) (B : A → type)
  (B/prop : (a : A) → IsProp (B a))
  (u,v : (a : A) × B a)
  (P : Path A (u.0) (v.0))
  : Path ((a : A) × B a) u v
  =
  λ i →
    < P i
    , let coe0 = coe 0 i (u.1) in λ j → B (P j) in
      let coe1 = coe 1 i (v.1) in λ j → B (P j) in
      B/prop (P i) coe0 coe1 i
     >


let PropSig
  (A : type) (B : A → type)
  (A/prop : IsProp A)
  (B/prop : (a : A) → IsProp (B a))
  : IsProp ((a : A) × B a)
  =
  λ u v →
    LemSig _ _ B/prop _ _ (A/prop (u.0) (v.0))


opaque
let PropIsContr (A : type) : IsProp (IsContr A) =
  λ contr →
    let A/prop : IsProp A =
      λ a b i →
        comp 1 0 (contr.1 a i) with
        | i=0 ⇒ λ _ → a
        | i=1 ⇒ λ j → contr.1 b j
        end
    in

    let contr/A/prop =
      PropSig A (λ a → (b : A) → Path A b a) A/prop
        (λ a → PropPi A (λ b → Path A b a) (λ b → PropSet A A/prop b a))
    in

    contr/A/prop contr

opaque
let PropIsEquiv (A,B : type) (f : A → B) : IsProp (IsEquiv A B f) =
  λ e0 e1 i b → PropIsContr (Fiber A B f b) (e0 b) (e1 b) i

opaque
let EquivLemma
  (A,B : type) (E0, E1 : Equiv A B)
  (P : Path (A → B) (E0.0) (E1.0))
  : Path (Equiv A B) E0 E1
  =
  LemSig (A → B) (IsEquiv A B) (PropIsEquiv A B) E0 E1 P


; per Dan Licata, UA and UABeta suffice for full univalence:
; https://groups.google.com/forum/#!topic/homotopytypetheory/j2KBIvDw53s

let UA (A,B : type) (E : Equiv A B) : Path^1 type A B =
  λ i →
    `(V i A B E)

let UA/beta
  (A,B : type) (E : Equiv A B) (a : A)
  : Path _ (coe 0 1 a in UA _ _ E) (E.0 a)
  =
  λ i →
    coe i 1 (E.0 a) in λ _ → B

let SigEquivToPath
  (A : type)
  (X : (B : type) × Equiv A B)
  : (B : type) × Path^1 type A B
  =
  < X.0
  , UA _ (X.0) (X.1)
  >

let SigPathToEquiv
  (A : type)
  (X : (B : type) × Path^1 type A B)
  : (B : type) × (Equiv A B)
  =
  < X.0
  , PathToEquiv _ (X.0) (X.1)
  >

opaque
let UA/retract
  (A,B : type)
  : Retract^3 (Equiv A B) (Path^1 type A B) (UA A B) (PathToEquiv A B)
  =
  λ E →
    EquivLemma _ _ (PathToEquiv _ _ (UA A B E)) E
      (λ i a → UA/beta A B E (coe 1 i a in λ _ → A) i)

let UA/retract/sig
  (A : type)
  : Retract^3 _ _ (SigEquivToPath A) (SigPathToEquiv A)
  =
  λ singl i →
    < singl.0
    , UA/retract A (singl.0) (singl.1) i
    >

opaque
let IsContrPath (A : type) : IsContr^1 ((B : _) × Path^1 type A B) =
  < <_, λ _ → A>
  , λ X i →
    < comp 0 1 A with
      | i=0 ⇒ X.1
      | i=1 ⇒ λ _ → A
      end
    , λ j →
      comp 0 j A with
      | i=0 ⇒ X.1
      | i=1 ⇒ λ _ → A
      end
    >
  >


; The following is a formulation of univalence proposed by Martin Escardo:
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
  < λ b → b
  , λ b →
    < <b, λ _ → b>
    , λ v i → <v.1 i, λ j → connection/or B (v.1) i j>
    >
  >

let univalence/alt (B : type) : IsContr^1 ((A : type) × Equiv A B) =
  < <B, IdEquiv/connection B>
  , λ w i →
       let VB : type = `(V i (car w) B (cdr w)) in
       let proj/B : VB → B = λ g → `(vproj i g (car w) B (cdr w)) in
       < VB
       , proj/B
       , λ b →
            let ctr/B : dim → B =
              λ j →
                comp 1 j b with
                | i=0 ⇒ λ k → w .1 .1 b .0 .1 k
                | i=1 ⇒ λ _ → b
                end
            in
            let ctr : Fiber VB B proj/B b =
              < `(vin i (car (car ((cdr (cdr w)) b))) (@ ctr/B 0)), λ l → ctr/B l >
            in
            < ctr
            , λ v j →
                let filler : dim → B =
                  λ l →
                    comp 1 l b with
                    | i=0 ⇒ λ k → w .1 .1 b .1 v j .1 k
                    | i=1 ⇒ λ k → connection/or B (v .1) j k
                    | j=0 ⇒ λ k → v .1 k
                    | j=1 ⇒ λ k → ctr/B k
                    end
                in
                < `(vin i (car (@ ((cdr ((cdr (cdr w)) b)) v) j)) (@ filler 0))
                , λ j → filler j
                >
            >
       >
  >

