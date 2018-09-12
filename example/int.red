import path
import void
import unit
import nat
import equivalence
import isotoequiv

data int where
| pos [n : nat]
| negsuc [n : nat]

let pred : int → int =
  λ [
  | pos n →
    elim n [
    | zero → negsuc zero
    | suc n → pos n
    ]
  | negsuc n → negsuc (suc n)
  ]

let isuc : int → int =
  λ [
  | pos n → pos (suc n)
  | negsuc n →
    elim n [
    | zero → pos zero
    | suc n → negsuc n
    ]
  ]

let pred-isuc : (n : int) → path int (pred (isuc n)) n =
  λ [
  | pos n → refl
  | negsuc n →
    elim n [
    | zero → refl
    | suc n → refl
    ]
  ]

let isuc-pred : (n : int) → path int (isuc (pred n)) n =
  λ [
  | pos n →
    elim n [
    | zero → refl
    | suc n' → refl
    ]
  | negsuc n → refl
  ]

let isuc/equiv : equiv int int =
  iso→equiv _ _ (isuc, (pred, (isuc-pred, pred-isuc)))

let iplus (m n : int) : int =
  elim m [
  | pos m →
    elim m [
    | zero → n
    | suc (n → m+n) → isuc m+n
    ]
  | negsuc m →
    elim m [
    | zero → pred n
    | suc (n → m+n) → pred m+n
    ]
  ]

let izero : int = pos zero

let iplus/unit-r : (n : int) → path int (iplus n izero) n =
  λ [
  | pos n →
    elim n [
    | zero → refl
    | suc (n → n+0) → λ i → isuc (n+0 i)
    ]
  | negsuc n →
    elim n [
    | zero → refl
    | suc (n → n+0) → λ i → pred (n+0 i)
    ]
  ]

let int-path/code : int → int → type =
  λ [
  | pos m → λ y →
    elim y [
    | pos n → nat/path/code m n
    | negsuc _ → void
    ]
  | negsuc m → λ y →
    elim y [
    | pos _ → void
    | negsuc n → nat/path/code m n
    ]
  ]

let int-refl : (x : int) → int-path/code x x =
  λ [
  | pos m → nat-refl m
  | negsuc m → nat-refl m
  ]

let int-path/encode (x y : int) (p : path int x y)
  : int-path/code x y
  =
  coe 0 1 (int-refl x) in λ i → int-path/code x (p i)

let int-repr : int → nat =
  λ [ pos m → m | negsuc m → m ]

let int/discrete : discrete int =
  λ [
  | pos m →
    λ [
    | pos n →
      or/elim (path nat m n) (neg (path nat m n))
        (or (path int (pos m) (pos n)) (neg (path int (pos m) (pos n))))
        (nat/discrete m n)
        (λ l → (tt, λ i → pos (l i)))
        (λ r → (ff, λ p → r (λ i → int-repr (p i))))
    | negsuc n → (ff, int-path/encode _ _)
    ]
  | negsuc m →
    λ [
    | pos n → (ff, int-path/encode _ _)
    | negsuc n →
      or/elim (path nat m n) (neg (path nat m n))
        (or (path int (negsuc m) (negsuc n)) (neg (path int (negsuc m) (negsuc n))))
        (nat/discrete m n)
        (λ l → (tt, λ i → negsuc (l i)))
        (λ r → (ff, λ p → r (λ i → int-repr (p i))))
    ]
  ]

let int/set : is-set int =
  discrete→set int int/discrete
