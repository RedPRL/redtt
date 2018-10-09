import path
import void
import unit
import hedberg

data nat where
| zero
| suc (x : nat)

def nat-pred : nat → nat =
  elim [
  | zero → zero
  | suc n → n
  ]


def nat-pred/suc (x : nat) : path nat x (nat-pred (suc x)) =
  refl

def plus (m n : nat) : nat =
  elim m [
  | zero → n
  | suc (m → plus/m/n) → suc plus/m/n
  ]

def plus/unit/l (n : nat) : path nat (plus zero n) n =
  refl

def plus/unit/r : (n : nat) → path nat (plus n zero) n =
  elim [
  | zero → refl
  | suc (n → path/n) → λ i → suc (path/n i)
  ]

def plus/assoc : (n m o : nat) → path nat (plus n (plus m o)) (plus (plus n m) o) =
  elim [
  | zero → refl
  | suc (n → plus/assoc/n) → λ m o i → suc (plus/assoc/n m o i)
  ]

def plus/suc/r : (n m : nat) → path nat (plus n (suc m)) (suc (plus n m)) =
  elim [
  | zero → refl
  | suc (n → plus/n/suc/r) → λ m i → suc (plus/n/suc/r m i)
  ]


def plus/comm : (m n : nat) → path nat (plus n m) (plus m n) =
  elim [
  | zero → plus/unit/r
  | suc (m → plus/comm/m) → λ n → trans _ (plus/suc/r n m) (λ i → suc (plus/comm/m n i))
  ]

def nat/path/code : nat → nat → type =
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

def nat-refl : (m : nat) → nat/path/code m m =
  elim [
  | zero → triv
  | suc (m' → nat-refl/m') → nat-refl/m'
  ]

def nat-path/encode (m n : nat) (p : path nat m n)
  : nat/path/code m n
  =
  coe 0 1 (nat-refl m) in λ i → nat/path/code m (p i)

def nat/discrete : discrete nat =
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

def nat/set : is-set nat =
 discrete→set nat nat/discrete
