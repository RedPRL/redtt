import path
import nat
import equivalence
import isotoequiv

data int where
| pos [n : nat]
| negsuc [n : nat]

let pred (x : int) : int =
  elim x [
  | pos n ⇒
    elim n [
    | zero ⇒ negsuc zero
    | suc n ⇒ pos n
    ]
  | negsuc n ⇒ negsuc (suc n)
  ]

let isuc (x : int) : int =
  elim x [
  | pos n ⇒ pos (suc n)
  | negsuc n ⇒
    elim n [
    | zero ⇒ pos zero
    | suc n ⇒ negsuc n
    ]
  ]


let pred-isuc (n : int) : Path int (pred (isuc n)) n =
  elim n [
  | pos n ⇒ λ _ → pos n
  | negsuc n ⇒
    elim n [
    | zero ⇒ λ _ → negsuc zero
    | suc n ⇒ λ _ → negsuc (suc n)
    ]
  ]

let isuc-pred (n : int) : Path int (isuc (pred n)) n =
  elim n [
  | pos n ⇒
    elim n [
    | zero ⇒ λ _ → pos zero
    | suc n' ⇒ λ _ → pos (suc n')
    ]
  | negsuc n ⇒ λ _ → negsuc n
  ]

let isuc-equiv : Equiv int int =
  Iso/Equiv _ _ < isuc, < pred, < isuc-pred, pred-isuc > > >
