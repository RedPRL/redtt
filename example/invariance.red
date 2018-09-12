import connection
import equivalence
import bool

-- This is ported from some RedPRL examples by Carlo Angiuli:
-- https://github.com/RedPRL/sml-redprl/blob/master/example/invariance.prl

let fun→pair (A : type) (f : bool → A) : A × A =
  (f tt, f ff)

let pair→fun (A : type) (p : A × A) : bool → A =
  λ b →
  elim b [
  | tt → p.fst
  | ff → p.snd
  ]

let fun→pair-is-equiv (A : type) : is-equiv^1 _ _ (fun→pair A) =
  λ p →
    ( (pair→fun A p, refl)
    , λ fib →
      coe 1 0 (λ i → (pair→fun _ (fib.snd i), λ j → weak-connection/or _ (fib.snd) i j))
      in λ j →
        path
          ((f : bool → A) × path (A × A) (f tt, f ff) p)
          (shannon/path A (fib.fst) j, fib.snd)
          (pair→fun A p, refl)
    )

let fun→pair/equiv (A : type) : equiv (bool → A) (A × A) =
  (fun→pair A, fun→pair-is-equiv A)

let fun→pair/path (A : type) : path^1 type (bool → A) (A × A) =
  ua (bool → A) (A × A) (fun→pair/equiv A)

let swap-pair (A : type) (p : A × A) : A × A =
  (p.snd, p.fst)

let swap-fun (A : type) : (bool → A) → bool → A =
  coe 1 0 (swap-pair A) in λ i →
    fun→pair/path A i → fun→pair/path A i

let swap-fun/path (A : type) : (f : bool → A) → path _ (swap-fun A (swap-fun A f)) f =
  coe 1 0 (λ _ → refl) in λ i →
    let swapcoe =
      coe 1 i (swap-pair A) in λ j →
        fun→pair/path A j → fun→pair/path A j
    in
    (f : fun→pair/path A i)
    → path (fun→pair/path A i)
        (swapcoe (swapcoe f))
        f
