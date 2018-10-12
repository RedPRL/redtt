import hlevel
import truncation
import equivalence
import isotoequiv

data (A : type) (R : A → A → type) ⊢ quotient where
| pt (a : A)
| gl (a b : A) (p : R a b) (i : 𝕀) [
  | i=0 → pt a
  | i=1 → pt b
  ]

-- A quotient by a type-theoretic equivalence relation *with coherences* is strongly effective.
def quotient/effective
  (A : type) (R : A → A → type)
  (R/refl : (a : A) → R a a)
  (R/symm : (a b : A) → R a b → R b a)
  (R/trans : (a b c : A) → R a b → R b c → R a c)
  (R/assoc
    : (a b c d : A) (p : R a b) (q : R b c) (r : R c d)
    → path (R a d) (R/trans _ _ _ (R/trans _ _ _ p q) r) (R/trans _ _ _ p (R/trans _ _ _ q r)))
  (R/inv-l : (a b : A) (p : R a b) → path _ (R/trans _ _ _ (R/symm _ _ p) p) (R/refl _))
  (R/inv-r : (a b : A) (p : R a b) → path _ (R/trans _ _ _ p (R/symm _ _ p)) (R/refl _))
  (R/idn-r : (a b : A) (p : R a b) → path _ (R/trans _ _ _ p (R/refl _)) p)
  : (a b : A)
  → path (quotient A R) (pt a) (pt b)
  → R a b
  =
  λ a b p →
  coe 0 1 (R/refl a) in λ i →
  elim (p i) [
  | pt b →
    R a b
  | gl b0 b1 b01 i →
    let g0 (x : R a b0) : R a b1 = R/trans _ _ _ x b01 in
    let g1 (x : R a b1) : R a b0 = R/trans _ _ _ x (R/symm _ _ b01) in
    let α0 (p : R a b1) =
      trans _
        (trans _
          (R/assoc a b1 b0 b1 p (R/symm b0 b1 b01) b01)
          (λ j → R/trans a b1 b1 p (R/inv-l b0 b1 b01 j)))
        (R/idn-r _ _ p)
    in
    let α1 (p : R a b0) =
      trans _
        (trans _
          (R/assoc a b0 b1 b0 p b01 (R/symm b0 b1 b01))
          (λ j → R/trans _ _ _ p (R/inv-r b0 b1 b01 j)))
        (R/idn-r _ _ p)
    in
    ua _ _ (iso→equiv _ _ (g0, g1, α0, α1)) i
  ]

-- Corollary: a quotient by a propositional equivalence relation is effective
def quotient/prop-valued/effective
  (A : type) (R : A → A → type)
  (R/prop : (a b : A) → is-prop (R a b))
  (R/refl : (a : A) → R a a)
  (R/symm : (a b : A) → R a b → R b a)
  (R/trans : (a b c : A) → R a b → R b c → R a c)
  : (a b : A)
  → path (quotient A R) (pt a) (pt b)
  → R a b
  =
  quotient/effective A R
    R/refl
    R/symm
    R/trans
    (λ _ _ _ _ _ _ _ → R/prop _ _ _ _)
    (λ _ _ _ → R/prop _ _ _ _)
    (λ _ _ _ → R/prop _ _ _ _)
    (λ _ _ _ → R/prop _ _ _ _)
