import path

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

let IdEquiv (A : type) : Equiv A A =
  < _
  , λ a →
    < <_, λ _ → a>
    , λ p i →
      let aux : Line A =
        λ j →
        comp 1 j a with
        | i=0 ⇒ λ k → p.cdr k   ; we should be able to eta-reduce this, but there is bug
        | i=1 ⇒ λ _ → a
        end
      in <aux 0, aux>
    >
  >


