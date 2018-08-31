import path
import void
import unit
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
  | pos n ⇒ refl
  | negsuc n ⇒
    elim n [
    | zero ⇒ refl
    | suc n ⇒ refl
    ]
  ]

let isuc-pred (n : int) : Path int (isuc (pred n)) n =
  elim n [
  | pos n ⇒
    elim n [
    | zero ⇒ refl
    | suc n' ⇒ refl
    ]
  | negsuc n ⇒ refl
  ]

let isuc-equiv : Equiv int int =
  Iso/Equiv _ _ <isuc, <pred, <isuc-pred, pred-isuc>>>

let iplus (m, n : int) : int =
  elim m [
  | pos m =>
    elim m [
    | zero => n
    | suc (n => m+n) => isuc m+n
    ]
  | negsuc m =>
    elim m [
    | zero => pred n
    | suc (n => m+n) => pred m+n
    ]
  ]

let izero : int = pos zero

let iplus/unit-r (n : int) : Path int (iplus n izero) n =
  elim n [
  | pos n =>
    elim n [
    | zero => refl
    | suc (n => n+0) => lam i -> isuc (n+0 i)
    ]
  | negsuc n =>
    elim n [
    | zero => refl
    | suc (n => n+0) => lam i -> pred (n+0 i)
    ]
  ]

let IntPathCode (x : int) : int → type =
  elim x [
  | pos m ⇒ λ y →
    elim y [
    | pos n ⇒ NatPathCode m n
    | negsuc _ ⇒ void
    ]
  | negsuc m ⇒ λ y →
    elim y [
    | pos _ ⇒ void
    | negsuc n ⇒ NatPathCode m n
    ]
  ]

let int-refl (x : int) : IntPathCode x x =
  elim x [
  | pos m ⇒ nat-refl m
  | negsuc m ⇒ nat-refl m
  ]

let int-path/encode (x,y : int) (p : Path int x y)
  : IntPathCode x y
  =
  coe 0 1 (int-refl x) in λ i → IntPathCode x (p i)

let int-repr (x : int) : nat =
  elim x [ pos m ⇒ m | negsuc m ⇒ m ]

let int/discrete : discrete int =
  λ x →
  elim x [
  | pos m ⇒ λ y →
    elim y [
    | pos n ⇒
      or/elim (Path nat m n) (neg (Path nat m n))
        (or (Path int (pos m) (pos n)) (neg (Path int (pos m) (pos n))))
        (nat/discrete m n)
        (λ l → <tt, λ i → pos (l i)>)
        (λ r → <ff, λ p → r (λ i → int-repr (p i))>)
    | negsuc n ⇒ <ff, int-path/encode _ _>
    ]
  | negsuc m ⇒ λ y →
    elim y [
    | pos n ⇒ <ff, int-path/encode _ _>
    | negsuc n ⇒
      or/elim (Path nat m n) (neg (Path nat m n))
        (or (Path int (negsuc m) (negsuc n)) (neg (Path int (negsuc m) (negsuc n))))
        (nat/discrete m n)
        (λ l → <tt, λ i → negsuc (l i)>)
        (λ r → <ff, λ p → r (λ i → int-repr (p i))>)
    ]
  ]

let int/set : IsSet int =
  discrete/to/set int int/discrete
