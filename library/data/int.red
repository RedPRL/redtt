import prelude
import data.nat

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

def int-repr : int → nat =
  elim [ pos m → m | negsuc m → m ]
