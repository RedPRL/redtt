import connection

; This is ported from some RedPRL examples by Carlo Angiuli:
; https://github.com/RedPRL/sml-redprl/blob/master/example/invariance.prl

let IsContr (C : type) : type =
  (c : _) × (c' : _) →
    Path C c' c

let Fiber (A : type) (B : type) (f : A → B) (b : B) : type =
  (a : _) × Path _ (f a) b

let IsEquiv (A : type) (B : type) (f : A → B) : type =
  (b : B) → IsContr (Fiber _ _ f b)

let Equiv (A : type) (B : type) : type =
  (f : A → B) × IsEquiv _ _ f

let fun-to-pair (A : type) (f : bool → A) : A × A =
  <f tt , f ff>

let pair-to-fun (A : type) (p : A × A) : bool → A =
  λ b → if b then p.car else p.cdr


; Dedicated to Bob ;-)
let shannon (A : type) (f : bool → A) : bool → A =
  λ b → if b then f tt else f ff

let shannon/path (A : type) (f : bool → A) : Path _ f (shannon A f) =
  funext _ _ _ _
    (λ b →
      if b with λ x →
        Path _ (f x) (shannon _ f x)
      then λ _ → f tt
      else λ _ → f ff)

let fun-to-pair-is-equiv (A : type) : IsEquiv^1 (_ → _) _ (fun-to-pair A) =
  λ pair →
    < <pair-to-fun A pair, λ _ → pair>
    , λ fib →
      coe 1 0
        (λ i →
          < λ b → if b then fib.cdr i .car else fib.cdr i .cdr
          , λ j → connection/or (A × A) (fun-to-pair A (fib.car)) pair (fib.cdr) i j
          >)
      in λ j →
        [i] (f : bool → A) × Path (A × A) <f tt, f ff> pair with
        | i=0 ⇒ < shannon/path A (fib.car) j, fib.cdr >
        | i=1 ⇒ < pair-to-fun A pair, λ _ → pair >
        end
    >

let fun-to-pair-equiv (A : type) : Equiv (bool → A) (A × A) =
  <fun-to-pair A, fun-to-pair-is-equiv A>

let fun-eq-pair (A : type) : Path^1 type (bool → A) (A × A) =
  λ i →
    `(V i (→ bool A) (× A A) (fun-to-pair-equiv A))

let swap-pair (A : type) (p : A × A) : A × A =
  <p.cdr, p.car>

let swap-fun (A : type) : (bool → A) → bool → A =
  coe 1 0 (swap-pair A) in λ i →
    (fun-eq-pair A i) → fun-eq-pair A i

let swap-fun-eqn (A : type) : (f : bool → A) → Path (bool → A) (swap-fun A (swap-fun A f)) f =
  coe 1 0 (λ pair _ → pair) in λ i →
    let swapcoe =
      coe 1 i (swap-pair A) in λ j →
        (fun-eq-pair A j) → fun-eq-pair A j
    in
    (f : fun-eq-pair A i)
    → Path (fun-eq-pair A i)
        (swapcoe (swapcoe f))
        f
