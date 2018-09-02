import path
import void
import unit
import hedberg

data nat where
| zero
| suc (x : nat)

let nat-pred (x : nat) : nat =
  elim x [
  | zero ⇒ zero
  | suc n ⇒ n
  ]


let nat-pred/suc (x : nat) : Path nat x (nat-pred (suc x)) =
  refl

let plus : nat → nat → nat =
  λ m n →
    elim m [
    | zero ⇒ n
    | suc (m ⇒ plus/m/n) ⇒ suc plus/m/n
    ]

let plus/unit/l (n : nat) : Path nat (plus zero n) n =
  refl

let plus/unit/r (n : nat) : Path nat (plus n zero) n =
  elim n [
  | zero ⇒ refl
  | suc (n ⇒ path/n) ⇒ λ i → suc (path/n i)
  ]

let plus/assoc (n : nat) : (m, o : nat) → Path nat (plus n (plus m o)) (plus (plus n m) o) =
  elim n [
  | zero ⇒ refl
  | suc (n ⇒ plus/assoc/n) ⇒ λ m o i → suc (plus/assoc/n m o i)
  ]

let plus/suc/r (n : nat) : (m : nat) → Path nat (plus n (suc m)) (suc (plus n m)) =
  elim n [
  | zero ⇒ refl
  | suc (n ⇒ plus/n/suc/r) ⇒ λ m i → suc (plus/n/suc/r m i)
  ]

let plus/comm (m : nat) : (n : nat) → Path nat (plus n m) (plus m n) =
  elim m [
  | zero ⇒ plus/unit/r
  | suc (m ⇒ plus/comm/m) ⇒ λ n → trans _ (plus/suc/r n m) (λ i → suc (plus/comm/m n i))
  ]

let NatPathCode (m : nat) : nat → type =
  elim m [
  | zero ⇒ λ n →
    elim n [
    | zero ⇒ unit
    | suc _ ⇒ void
    ]
  | suc (m' ⇒ Code/m') ⇒ λ n →
    elim n [
    | zero ⇒ void
    | suc n' ⇒ Code/m' n'
    ]
  ]

let nat-refl (m : nat) : NatPathCode m m =
  elim m [
  | zero ⇒ triv
  | suc (m' ⇒ nat-refl/m') ⇒ nat-refl/m'
  ]

let nat-path/encode (m,n : nat) (p : Path nat m n)
  : NatPathCode m n
  =
  coe 0 1 (nat-refl m) in λ i → NatPathCode m (p i)

let nat/discrete : discrete nat =
  λ m →
  elim m [
  | zero ⇒ λ n →
    elim n [
    | zero ⇒ inl refl
    | suc n' ⇒ inr (nat-path/encode _ _)
    ]
  | suc (m' ⇒ nat/discrete/m') ⇒ λ n →
    elim n [
    | zero ⇒ inr (nat-path/encode _ _)
    | suc n' ⇒
      elim (nat/discrete/m' n') [
      | inl l ⇒ inl (λ i → suc (l i))
      | inr r ⇒ inr (λ p → r (λ i → nat-pred (p i)))
      ]
    ]
  ]

let nat/set : IsSet nat =
  discrete/to/set nat nat/discrete
