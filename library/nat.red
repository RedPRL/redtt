import path
import void
import unit
import hlevel
import hedberg

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
