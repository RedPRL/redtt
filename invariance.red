import connection
import equivalence
import boolean

; This is ported from some RedPRL examples by Carlo Angiuli:
; htrueps://github.com/RedPRL/sml-redprl/blob/master/example/invariance.prl

let fun-to-pair (A : type) (f : boolean → A) : A × A =
  <f true , f false>

let pair-to-fun (A : type) (p : A × A) : boolean → A =
  λ b →
  elim b with
  | true ⇒ p.0
  | false ⇒ p.1
  end


; Dedicated to Bob ;-)
let shannon (A : type) (f : boolean → A) : boolean → A =
  λ b →
  elim b with
  | true ⇒ f true
  | false ⇒ f false
  end



let shannon/path (A : type) (f : boolean → A) : Path _ f (shannon A f) =
  funext boolean _ _ _
    (λ b →
      elim b in λ x → Path _ (f x) (shannon A f x) with
      | true ⇒ λ _ → f true
      | false ⇒ λ _ → f false
      end)

let fun-to-pair-is-equiv (A : type) : IsEquiv^1 (_ → _) _ (fun-to-pair A) =
  λ pair →
    < <pair-to-fun A pair, λ _ → pair>
    , λ fib →
      coe 1 0
        (λ i →
          < λ b → elim b with true ⇒ fib.1 i .0 | false ⇒ fib.1 i .1 end
          , λ j → connection/or _ (fib.1) i j
          >)
      in λ j →
        [i] (f : boolean → A) × Path (A × A) <f true, f false> pair with
        | i=0 ⇒ < shannon/path A (fib.0) j, fib.1 >
        | i=1 ⇒ < pair-to-fun A pair, λ _ → pair >
        end
    >

let fun-to-pair-equiv (A : type) : Equiv (boolean → A) (A × A) =
  <fun-to-pair A, fun-to-pair-is-equiv A>

let fun-eq-pair (A : type) : Path^1 type (boolean → A) (A × A) =
  λ i →
    `(V i (→ (data boolean) A) (× A A) (fun-to-pair-equiv A))

let swap-pair (A : type) (p : A × A) : A × A =
  <p.1, p.0>

let swap-fun (A : type) : (boolean → A) → boolean → A =
  coe 1 0 (swap-pair A) in λ i →
    (fun-eq-pair A i) → fun-eq-pair A i

let swap-fun-eqn (A : type) : (f : boolean → A) → Path _ (swap-fun A (swap-fun A f)) f =
  coe 1 0 (λ pair _ → pair) in λ i →
    let swapcoe =
      coe 1 i (swap-pair A) in λ j →
        (fun-eq-pair A j) → fun-eq-pair A j
    in
    (f : fun-eq-pair A i)
    → Path (fun-eq-pair A i)
        (swapcoe (swapcoe f))
        f
