import path
import void
import unit
import nat
import hlevel
import equivalence
import isotoequiv
import hedberg

def isuc/equiv : equiv int int =
  iso→equiv _ _ (isuc, (pred, (isuc-pred, pred-isuc)))

def int-path/code : int → int → type =
  elim [
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

def int-refl : (x : int) → int-path/code x x =
  elim [
  | pos m → nat-refl m
  | negsuc m → nat-refl m
  ]

def int-path/encode (x y : int) (p : path int x y)
  : int-path/code x y
  =
  coe 0 1 (int-refl x) in λ i → int-path/code x (p i)

def int/discrete : discrete int =
  elim [
  | pos m →
    elim [
    | pos n →
      elim (nat/discrete m n) [
      | inl l → inl (λ i → pos (l i))
      | inr r → inr (λ p → r (λ i → int-repr (p i)))
      ]
    | negsuc n → inr (int-path/encode _ _)
    ]
  | negsuc m →
    elim [
    | pos n → inr (int-path/encode _ _)
    | negsuc n →
      elim (nat/discrete m n) [
      | inl l → inl (λ i → negsuc (l i))
      | inr r → inr (λ p → r (λ i → int-repr (p i)))
      ]
    ]
  ]

def int/set : is-set int =
  discrete→set int int/discrete
