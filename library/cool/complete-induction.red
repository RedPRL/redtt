import prelude
import data.nat
import data.unit
import data.void
import data.or

def le : nat → nat → type =
  elim [
  | zero → λ _ → unit
  | suc (m → f) →
    elim [
    | zero → void
    | suc n → f n
    ]
  ]

def le/suc/right : (n m : nat) → le n m → le n (suc m) =
  elim [
  | zero → λ _ _ →  triv
  | suc (n' → f) → elim [
    | zero → elim []
    | suc m' → λ l → f m' l
    ]
  ]

def le/suc : (n m : nat) → le n m → le (suc n) (suc m) =
  elim [
  | zero → λ _ _ →  triv
  | suc _ → λ _ l → l
  ]

def le/refl : (n : nat) → le n n =
  elim [
  | zero → triv
  | suc (_ → f) → f
  ]

def le/zero/implies/zero : (n : nat) → (le n zero) → path nat zero n =
  elim [
  | zero → λ _ → refl
  | suc n' → elim []
  ]

def le/case : (m n : nat) → (le n (suc m)) → or (path nat n (suc m)) (le n m) =
  elim [
  | zero →
    elim [
    | zero → λ _ → inr triv
    | suc n' →
      elim n' [
      | zero → λ _ → inl refl
      | suc _ → λ p → inr p
      ]
    ]
  | suc (m' → c) →
    elim [
    | zero → λ _ → inr triv
    | suc n' → λ p →
      elim (c n' p) [
      | inl p → inl (λ i → suc (p i))
      | inr l → inr (le/suc n' m' l)
      ]
    ]
  ]

def weak/induction (P : nat → type) : type =
  P zero
  → ((n : nat) → P n → P (suc n))
  → (n : nat)
  → P n

def realize/weak/induction (P : nat → type) : weak/induction P =
  λ p0 ps →
  elim [
  | zero → p0
  | suc (n' → pn') → ps n' pn'
  ]

def complete/induction (P : nat → type) : type =
  P zero
  → ((n : nat) → ((k : nat) → (le k n) → P k) → P (suc n))
  → (n : nat)
  → P n

def complete/implies/weak
  (P : nat → type)
  (complete : complete/induction P)
  : weak/induction P
  =
  λ p0 ps →
  complete p0 (λ n f → ps n (f n (le/refl n)))

def weak/implies/complete
  (P : nat → type)
  (weak : (P' : nat → type) → weak/induction P')
  : complete/induction P
  =
  λ p0 ps →
  let P' (n : nat) : type = (k : nat) → (le k n) → P k in
  let P'0 : P' zero =
    λ k k/le/0 →
    coe 0 1 p0 in λ i →
    P (le/zero/implies/zero k k/le/0 i)
  in
  let f (n : nat) (p'n : P' n) : (P' (suc n)) =
    λ k k/le/sn →
    elim (le/case n k k/le/sn) [
    | inl p → coe 1 0 (ps n p'n) in λ i → P (p i)
    | inr l → p'n k l
    ]
  in
  let P'n : (n : nat) → P' n = weak P' P'0 f in
  λ n → P'n n n (le/refl n)

-- prove that a gcd exists for any m, n using complete induction
-- examine the running code for its time complexity
-- consider other representations of natural numbers and their associated induction princ's
-- (0, 2n, 2n+1) doesn't help gcd, what would?
-- understanding information flow in a proof in terms of homotopy levels, eg, and consider suppressing irrelevant information
