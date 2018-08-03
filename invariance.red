import connection
import equivalence

; This is ported from some RedPRL examples by Carlo Angiuli:
; https://github.com/RedPRL/sml-redprl/blob/master/example/invariance.prl

let fun-to-pair (A : type) (f : bool → A) : A × A =
  <f tt , f ff>

let pair-to-fun (A : type) (p : A × A) : bool → A =
  λ b → if b then p.0 else p.1


; Dedicated to Bob ;-)
let shannon (A : type) (f : bool → A) : bool → A =
  λ b → if b then f tt else f ff

let shannon/path (A : type) (f : bool → A) : Path _ f (shannon A f) =
  funext _ _ _ _
    (λ b →
      if b in λ x →
        Path _ (f x) (shannon _ f x)
      then λ _ → f tt
      else λ _ → f ff)

let fun-to-pair-is-equiv (A : type) : IsEquiv^1 (_ → _) _ (fun-to-pair A) =
  λ pair →
    < <pair-to-fun A pair, λ _ → pair>
    , λ fib →
      coe 1 0
        (λ i →
          < λ b → if b then fib.1 i .0 else fib.1 i .1
          , λ j → connection/or _ (fib.1) i j
          >)
      in λ j →
        [i] (f : bool → A) × Path (A × A) <f tt, f ff> pair with
        | i=0 ⇒ < shannon/path A (fib.0) j, fib.1 >
        | i=1 ⇒ < pair-to-fun A pair, λ _ → pair >
        end
    >

let fun-to-pair-equiv (A : type) : Equiv (bool → A) (A × A) =
  <fun-to-pair A, fun-to-pair-is-equiv A>

let fun-eq-pair (A : type) : Path^1 type (bool → A) (A × A) =
  λ i →
    `(V i (→ bool A) (× A A) (fun-to-pair-equiv A))

let swap-pair (A : type) (p : A × A) : A × A =
  <p.1, p.0>

let swap-fun (A : type) : (bool → A) → bool → A =
  coe 1 0 (swap-pair A) in λ i →
    (fun-eq-pair A i) → fun-eq-pair A i

let swap-fun-eqn (A : type) : (f : bool → A) → Path _ (swap-fun A (swap-fun A f)) f =
  coe 1 0 (λ pair _ → pair) in λ i →
    let swapcoe =
      coe 1 i (swap-pair A) in λ j →
        (fun-eq-pair A j) → fun-eq-pair A j
    in
    (f : fun-eq-pair A i)
    → Path (fun-eq-pair A i)
        (swapcoe (swapcoe f))
        f
