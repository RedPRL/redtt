import path

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
; the code in this file is adapted from yacctt and redprl



let IdEquiv (A : type) : Equiv A A =
  < _
  , λ a →
    < <_, λ _ → a>
    , λ p i →
      let aux : Line A =
        λ j →
        comp 1 j a with
        | i=0 ⇒ p.cdr
        | i=1 ⇒ λ _ → a
        end
      in <aux 0, aux>
    >
  >

; per Dan Licata, UA and UABeta suffice for full univalence:
; https://groups.google.com/forum/#!topic/homotopytypetheory/j2KBIvDw53s

let UA (A : type) (B : type) (E : Equiv A B) : Path type A B =
  λ i →
    `(V i A B E)

let UA/beta
  (A : type) (B : type) (E : Equiv A B) (a : A)
  : Path _ (coe 0 1 a in UA _ _ E) (E.car a)
  =
  λ i →
    coe i 1 (E.car a) in λ _ → B


; To prove univalence from UA and UABeta, we need some basic results.
; (What follows is adapted from the cubicaltt and RedPRL developments.)


let PathToEquiv
  (A : type) (B : type) (P : Path type A B)
  : Equiv A B
  =
  coe 0 1 (IdEquiv A) in λ i → Equiv A (P i)


let Retract (A : type) (B : type) (f : A → B) (g : B → A) : type =
  (a : A) →
    Path A (g (f a)) a

; The following exhibits a bug
let EquivLemmaType (A : type) (B : type)
  : Retract^3 (Equiv A B) (Path^1 type A B) (UA A B) (PathToEquiv A B)
  = ?

