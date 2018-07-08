import path
import connection

; the code in this file is adapted from yacctt and redprl

let IsContr (C : type) : type =
  (c : _) × (c' : _) →
    Path C c' c

let Fiber (A : type) (B : type) (f : A → B) (b : B) : type =
  (a : _) × Path _ (f a) b

let IsEquiv (A : type) (B : type) (f : A → B) : type =
  (b : B) → IsContr (Fiber _ _ f b)

let Equiv (A : type) (B : type) : type =
  (f : A → B) × IsEquiv _ _ f

let IsProp (C : type) : type =
  (c : _) (c' : _) →
    Path C c c'

let IsSet (C : type) : type =
  (c : _) (c' : _) →
    IsProp (Path C c c')


let Retract (A : type) (B : type) (f : A → B) (g : B → A) : type =
  (a : A) →
    Path A (g (f a)) a

let RetIsContr
  (A : type) (B : type)
  (f : A → B)
  (g : B → A)
  (h : Retract A B f g)
  (c : IsContr B)
  : IsContr A
  =
  < g (c.car),
    λ a i →
      comp 0 1 (g (c.cdr (f a) i)) with
      | i=0 ⇒ h a
      | i=1 ⇒ λ _ → g (c.car)
      end
  >

let IdEquiv (A : type) : Equiv A A =
  < λ a → a
  , λ a →
    < <a, λ _ → a>
    , λ p i →
      let aux : Line A =
        λ j →
        comp 1 j a with
        | i=0 ⇒ λ k → p.cdr k
        | i=1 ⇒ λ _ → a
        end
      in
      <aux 0, λ j → aux j>
    >
  >

let PathToEquiv
  (A : type) (B : type) (P : Path^1 type A B)
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
  (u : (a : A) × B a)
  (v : (a : A) × B a)
  (P : Path A (u.car) (v.car))
  : Path ((a : A) × B a) u v
  =
  λ i →
    < P i
    , let coe0 = coe 0 i (u.cdr) in λ j → B (P j) in
      let coe1 = coe 1 i (v.cdr) in λ j → B (P j) in
      B/prop (P i) coe0 coe1 i
     >


let PropSig
  (A : type) (B : A → type)
  (A/prop : IsProp A)
  (B/prop : (a : A) → IsProp (B a))
  : IsProp ((a : A) × B a)
  =
  λ u v →
    LemSig _ _ B/prop _ _ (A/prop (u.car) (v.car))


opaque
let PropIsContr (A : type) : IsProp (IsContr A) =
  λ contr →
    let A/prop : IsProp A =
      λ a b i →
        comp 1 0 (contr.cdr a i) with
        | i=0 ⇒ λ _ → a
        | i=1 ⇒ λ j → contr.cdr b j
        end
    in

    let contr/A/prop =
      PropSig A (λ a → (b : A) → Path A b a) A/prop
        (λ a → PropPi A (λ b → Path A b a) (λ b → PropSet A A/prop b a))
    in

    contr/A/prop contr

opaque
let PropIsEquiv (A : type) (B : type) (f : A → B) : IsProp (IsEquiv A B f) =
  λ e0 e1 i b → PropIsContr (Fiber A B f b) (e0 b) (e1 b) i

opaque
let EquivLemma
  (A : type) (B : type) (E0 : Equiv A B) (E1 : Equiv A B)
  (P : Path (A → B) (E0.car) (E1.car))
  : Path (Equiv A B) E0 E1
  =
  LemSig (A → B) (IsEquiv A B) (PropIsEquiv A B) E0 E1 P


; per Dan Licata, UA and UABeta suffice for full univalence:
; https://groups.google.com/forum/#!topic/homotopytypetheory/j2KBIvDw53s

let UA (A : type) (B : type) (E : Equiv A B) : Path^1 type A B =
  λ i →
    `(V i A B E)

let UA/beta
  (A : type) (B : type) (E : Equiv A B) (a : A)
  : Path _ (coe 0 1 a in UA _ _ E) (E.car a)
  =
  λ i →
    coe i 1 (E.car a) in λ _ → B

let SigEquivToPath
  (A : type)
  (X : (B : type) × Equiv A B)
  : (B : type) × Path^1 type A B
  =
  < X.car
  , UA A (X.car) (X.cdr)
  >

let SigPathToEquiv
  (A : type)
  (X : (B : type) × Path^1 type A B)
  : (B : type) × (Equiv A B)
  =
  < X.car
  , PathToEquiv A (X.car) (X.cdr)
  >

opaque
let UA/retract
  (A : type) (B : type)
  : Retract^3 (Equiv A B) (Path^1 type A B) (UA A B) (PathToEquiv A B)
  =
  λ E →
    EquivLemma A B (PathToEquiv A B (UA A B E)) E
      (λ i a → UA/beta A B E (coe 1 i a in λ _ → A) i)

opaque
let UA/retract/sig
  (A : type)
  : Retract^3
      ((B : type) × Equiv A B)
      ((B : type) × Path^1 type A B)
      (SigEquivToPath A)
      (SigPathToEquiv A)
  =
  λ singl i →
    < singl.car
    , UA/retract A (singl.car) (singl.cdr) i
    >

opaque
let IsContrPath (A : type) : IsContr^1 ((B : type) × Path^1 type A B) =
  < <_, λ _ → A>
  , λ X i →
    < comp 0 1 A with
      | i=0 ⇒ X.cdr
      | i=1 ⇒ λ _ → A
      end
    , λ j →
      comp 0 j A with
      | i=0 ⇒ X.cdr
      | i=1 ⇒ λ _ → A
      end
    >
  >


; The following is a formulation of univalence proposed by Martin Escardo:
; https://groups.google.com/forum/#!msg/homotopytypetheory/HfCB_b-PNEU/Ibb48LvUMeUJ
; See also Theorem 5.8.4 of the HoTT Book.

let univalence (A : type) : IsContr^1 ((B : type) × Equiv A B) =
  RetIsContr^1
    ((B : type) × Equiv A B)
    ((B : type) × Path^1 type A B)
    (SigEquivToPath A)
    (SigPathToEquiv A)
    (UA/retract/sig A)
    (IsContrPath A)

let IdEquiv/connection (B : type) : Equiv B B =
  < λ b → b
  , λ b →
    < <b, λ _ → b>
    , λ v i → <v.cdr i, λ j → connection/or B (v.car) b (v.cdr) i j>
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
            let ctr/B : Line B =
              λ j →
                comp 1 j b with
                | i=0 ⇒ λ k → w .cdr .cdr b .car .cdr k
                | i=1 ⇒ λ _ → b
                end
            in
            let ctr : Fiber VB B proj/B b =
              < `(vin i (car (car ((cdr (cdr w)) b))) (@ ctr/B 0)), λ l → ctr/B l >
            in
            < ctr
            , λ v j →
                let filler : Line B =
                  λ l →
                    comp 1 l b with
                    | i=0 ⇒ λ k → w .cdr .cdr b .cdr v j .cdr k
                    | i=1 ⇒ λ k → connection/or B (v .car) b (v .cdr) j k
                    | j=0 ⇒ λ k → v .cdr k
                    | j=1 ⇒ λ k → ctr/B k
                    end
                in
                < `(vin i (car (@ ((cdr ((cdr (cdr w)) b)) v) j)) (@ filler 0))
                , λ j → filler j
                >
            >
       >
  >

