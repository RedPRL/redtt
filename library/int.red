import path
import void
import unit
import nat
import hlevel
import equivalence
import isotoequiv
import hedberg

data int where
| pos (n : nat)
| negsuc (n : nat)

def pred : int → int =
  elim [
  | pos n →
    elim n [
    | zero → negsuc zero
    | suc n → pos n
    ]
  | negsuc n → negsuc (suc n)
  ]

def isuc : int → int =
  elim [
  | pos n → pos (suc n)
  | negsuc n →
    elim n [
    | zero → pos zero
    | suc n → negsuc n
    ]
  ]

def pred-isuc : (n : int) → path int (pred (isuc n)) n =
  elim [
  | negsuc * → refl
  | * → refl
  ]

def isuc-pred : (n : int) → path int (isuc (pred n)) n =
  elim [
  | pos * → refl
  | * → refl
  ]

def isuc/equiv : equiv int int =
  iso→equiv _ _ (isuc, (pred, (isuc-pred, pred-isuc)))

def iplus (m n : int) : int =
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

def izero : int = pos zero

def iplus/unit-r : (n : int) → path int (iplus n izero) n =
  elim [
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

def int-repr : int → nat =
  elim [ pos m → m | negsuc m → m ]

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
