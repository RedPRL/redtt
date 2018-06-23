import connection

let IsContr (C : type) : type =
  (c : _) × (c' : _) →
    Path C c' c

let Fiber (A : type) (B : type) (f : A → B) (b : B) : type =
  (a : _) × Path _ (f a) b

let IsEquiv (A : type) (B : type) (f : A → B) : type =
  (b : B) → IsContr (Fiber _ _ f b)

let Equiv (A : type) (B : type) : type =
  (f : A → B) × IsEquiv _ _ f

let fun-to-pair (A : type) (f : bool → type) : type × type =
  <f tt , f ff>

let pair-to-fun (A : type) (p : type × type) : bool → type =
  λ b → if b then p.car else p.cdr


; Dedicated to Bob ;-)
let shannon (A : type) (f : bool → A) : bool → A =
  λ b → if b then f tt else f ff

let shannon/path (A : type) (f : bool → A) : Path _ f (shannon A f) =
  funext _ _ _ _
    (λ b →
      if b with λ x →
        Path A (f x) (shannon A f x)
      then λ _ → f tt
      else λ _ → f ff)

let fun-to-pair-is-equiv (A : type) : IsEquiv^1 (_ → _) _ (fun-to-pair A) =
  λ pair →
    < <pair-to-fun A pair, λ _ → pair>
    , λ fib →
      coe 1 0
        (λ i →
          < λ b → if b then fib.cdr i .car else fib.cdr i .cdr
          , λ j → connection/or^1 (type × type) (fun-to-pair A (fib.car)) pair (fib.cdr) i j
          >)
      in λ j →
        [i] (f : bool → type) × Path^1 (type × type) <f tt, f ff> pair with
        | i=0 ⇒ < shannon/path^1 type (fib.car) j, fib.cdr >
        | i=1 ⇒ < pair-to-fun A pair, λ _ → pair >
        end
    >

