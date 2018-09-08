import connection
import equivalence
import bool

; This is ported from some RedPRL examples by Carlo Angiuli:
; https://github.com/RedPRL/sml-redprl/blob/master/example/invariance.prl

let fun-to-pair (A : type) (f : bool → A) : A × A =
  (f tt , f ff)

let pair-to-fun (A : type) (p : A × A) : bool → A =
  λ b →
  elim b [
  | tt → p.fst
  | ff → p.snd
  ]

let fun-to-pair-is-equiv (A : type) : IsEquiv^1 _ _ (fun-to-pair A) =
  λ p →
    ( (pair-to-fun A p, refl)
    , λ fib →
      coe 1 0
        (λ i →
          ( λ b → elim b [ tt → fib.snd i .fst | ff → fib.snd i .snd ]
          , λ j → weak-connection/or _ (fib.snd) i j
          ))
      in λ j →
        [i] (f : bool → A) × Path (A × A) (f tt, f ff) p [
        | i=0 → (shannon/path A (fib.fst) j, fib.snd)
        | i=1 → (pair-to-fun A p, refl)
        ]
    )

let fun-to-pair-equiv (A : type) : Equiv (bool → A) (A × A) =
  (fun-to-pair A, fun-to-pair-is-equiv A)

let fun-eq-pair (A : type) : Path^1 type (bool → A) (A × A) =
  λ i →
    `(V i (→ (data bool) A) (× A A) (fun-to-pair-equiv A))

let swap-pair (A : type) (p : A × A) : A × A =
  (p.snd, p.fst)

let swap-fun (A : type) : (bool → A) → bool → A =
  coe 1 0 (swap-pair A) in λ i →
    fun-eq-pair A i → fun-eq-pair A i

let swap-fun-eqn (A : type) : (f : bool → A) → Path _ (swap-fun A (swap-fun A f)) f =
  coe 1 0 (λ p _ → p) in λ i →
    let swapcoe =
      coe 1 i (swap-pair A) in λ j →
        fun-eq-pair A j → fun-eq-pair A j
    in
    (f : fun-eq-pair A i)
    → Path (fun-eq-pair A i)
        (swapcoe (swapcoe f))
        f
