import data.nat
import data.unit 
import data.void
import prelude
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
  | zero → λ _ _ → ★
  | suc (n' → f) →
    elim [
    | zero → elim []
    | suc m' → λ l → f m' l
    ]
  ]

def le/suc : (n m : nat) → le n m → le (suc n) (suc m) =
  elim [
  | zero → λ _ _ → ★
  | suc _ → λ _ l → l
  ]

def le/refl : (n : nat) → le n n =
  elim [
  | zero → ★
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
    | zero → λ _ → inr ★
    | suc n' →
      elim n' [
      | zero → λ _ → inl refl
      | suc _ → λ p → inr p
      ]
    ]
  | suc (m' → c) →
    elim [
    | zero → λ _ → inr ★
    | suc n' → λ p →
      elim (c n' p) [
      | inl p → inl (λ i → suc (p i))
      | inr l → inr (le/suc n' m' l)
      ]
    ]
  ]

def sub/le : (n m : nat) → le (sub n m) n =
  elim [
  | zero → λ _ → ★
  | suc (n' → f) → λ m → elim m [
    | zero → le/refl n'
    | suc m' → le/suc/right (sub n' m') n' (f m')
    ]
  ]

def sub/zero/id (n : nat) : path _ (sub n zero) n = 
  elim n [
  | zero → refl
  | suc n' → refl
  ]

def sub/zero/zero/eq (n : nat) 
  : (m : nat) → path _ (sub n m) zero → path _ (sub m n) zero → path _ n m =
  elim n [
  | zero → λ m p1 p2 → trans _ (symm _ p2) (sub/zero/id m)
  | suc (n' → f) → elim [
    | zero → λ p _ → p
    | suc m' → λ p1 p2 → λ i → suc (f m' p1 p2 i)
    ] 
  ]

def sub/le/implies/le : (m n k : nat) → path nat (suc k) (sub m n) → le n m =
  elim [
  | zero →
    elim [
    | zero → λ _ _ → ★
    | suc n' → λ _ p → coe 1 0 ★ in λ i → le (p i) zero
    ]
  | suc (m' → f) →
    elim [
    | zero → λ _ _ → ★
    | suc n' → f n'
    ]
  ]

/- where's the hole?

def eq/sub/zero : (m n : nat) → path nat m n → path nat (sub m n) zero =
  elim [
  | zero → refl
	| suc (m' → f) → 
    elim [
    | zero → refl
    | suc n' → λ p → 
      let p' : path nat m' n' = λ i → nat-pred (p i) in
			f n' p'
    ]
  ]
-/

def plus/rinv/sub : (m n k : nat) → path nat k (sub m n) → le n m → path nat (plus k n) m =
  elim [
  | zero → 
    elim [
    | zero → λ k p _ → trans _ (eta k) p
    | suc n' → λ _ _ p → elim p []
    ]
  | suc (m' → f) → 
    elim [
    | zero → λ k p _ → trans _ (eta k) p
    | suc n' → λ k p l → 
      let p' : path nat (suc (plus k n')) (suc m') = λ i → suc (f n' k p l i) in
      trans _ (plus/suc/r k n') p' 
    ]
  ]
