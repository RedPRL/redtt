import nat
import path
import unit

def transport (A : type) (M N : A) (p : path A M N) (C : A → type) : C M →  C N =
  λ cm → coe 0 1 cm in λ i → C (p i)

def le : nat → nat → type =
  elim [
  | zero → λ _ → unit
  | suc (m' → f) →
    elim [
    | zero → void
    | suc n' → f n'
    ]
  ]

def le/suc : (n m : nat) → le n m → le (suc n) (suc m) =
  elim [
  | zero → λ _ _ →  triv
  | suc n' → λ m' l → l
  ]

def eq/implies/le (n : nat) : le n n =
  elim n [
  | zero → triv
  | suc (n' → f) → f
  ]

def le/zero/implies/zero : (n : nat) →  (le n zero) → path nat zero n =
  elim [
  | zero → λ _ → refl
  | suc n' → λ p → elim p []
  ]

def le/case : (m n : nat) →  (le n (suc m)) →  or (path nat n (suc m)) (le n m) =
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
    | zero → λ _ →  inr triv
    | suc n' → λ p →
      elim (c n' p) [
      | inl p → inl (λ i -> suc (p i))
      | inr l → inr (le/suc n' m' l)
      ]
    ]
  ]

def weak/induction (P : nat → type) : type =
  (P zero) → ((n : nat) → P n → P (suc n)) → ((n : nat) → P n)

def complete/induction (P : nat → type) : type =
  (P zero) → ((n : nat) → ((k : nat) → (le k n) → P k) → P (suc n)) → ((n : nat) → P n)

def complete/implies/weak (P : nat → type) : complete/induction P → weak/induction P =
  λ complete p0 ps → complete p0 (λ n f → ps n (f n (eq/implies/le n)))

def weak/implies/complete : (P : nat → type) →
  ((P' : nat → type) → weak/induction P') → complete/induction P =
  λ P weak p0 ps →
    let P' : nat → type = λ n → (k : nat) → (le k n) → P k in
    let P'0 : P' zero = λ k k/le/0 → transport nat zero k (le/zero/implies/zero k k/le/0) P p0 in
    let f (n : nat) (p'n : P' n) : (P' (suc n)) =
      λ k k/le/sn →
      elim (le/case n k k/le/sn) [
      | inl p → transport nat (suc n) k (symm nat p) P (ps n p'n)
      | inr l → p'n k l
      ]
    in
    let P'n : ((n : nat) → P' n) = (weak P') P'0 f in
    λ n → P'n n n (eq/implies/le n)
