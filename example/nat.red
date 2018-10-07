import path
import void
import unit
import hedberg

data nat where
| zero
| suc (x : nat)

let nat-pred : nat → nat =
  elim [
  | zero → zero
  | suc n → n
  ]


let nat-pred/suc (x : nat) : path nat x (nat-pred (suc x)) =
  refl

let plus (m n : nat) : nat =
  elim m [
  | zero → n
  | suc (m → plus/m/n) → suc plus/m/n
  ]

let plus/unit/l (n : nat) : path nat (plus zero n) n =
  refl

let plus/unit/r : (n : nat) → path nat (plus n zero) n =
  elim [
  | zero → refl
  | suc (n → path/n) → λ i → suc (path/n i)
  ]

let plus/assoc : (n m o : nat) → path nat (plus n (plus m o)) (plus (plus n m) o) =
  elim [
  | zero → refl
  | suc (n → plus/assoc/n) → λ m o i → suc (plus/assoc/n m o i)
  ]

let plus/suc/r : (n m : nat) → path nat (plus n (suc m)) (suc (plus n m)) =
  elim [
  | zero → refl
  | suc (n → plus/n/suc/r) → λ m i → suc (plus/n/suc/r m i)
  ]


let plus/comm : (m n : nat) → path nat (plus n m) (plus m n) =
  elim [
  | zero → plus/unit/r
  | suc (m → plus/comm/m) → λ n → trans _ (plus/suc/r n m) (λ i → suc (plus/comm/m n i))
  ]

let nat/path/code : nat → nat → type =
  elim [
  | zero →
    elim [
    | zero → unit
    | suc _ → void
    ]
  | suc (m' → code/m') →
    elim [
    | zero → void
    | suc n' → code/m' n'
    ]
  ]

let nat-refl : (m : nat) → nat/path/code m m =
  elim [
  | zero → triv
  | suc (m' → nat-refl/m') → nat-refl/m'
  ]

let nat-path/encode (m n : nat) (p : path nat m n)
  : nat/path/code m n
  =
  coe 0 1 (nat-refl m) in λ i → nat/path/code m (p i)

let nat/discrete : discrete nat =
  elim [
  | zero →
    elim [
    | zero → inl refl
    | suc n' → inr (nat-path/encode zero (suc n'))
    ]
  | suc (m' → nat/discrete/m') →
    elim [
    | zero → inr (nat-path/encode (suc m') zero)
    | suc n' →
      elim (nat/discrete/m' n') [
      | inl l → inl (λ i → suc (l i))
      | inr r → inr (λ p → r (λ i → nat-pred (p i)))
      ]
    ]
  ]

let nat/set : is-set nat =
 discrete→set nat nat/discrete
