import prelude
import data.nat

data (A : type) ⊢ list where
| nil
| cons (x : A) (xs : list)

def tail (A : type) : list A → list A =
  elim [
  | nil → nil
  | cons _ xs → xs
  ]

def length (A : type) : list A → nat =
  elim [
  | nil → zero
  | cons _ (_ → n) → suc n
  ]

def append (A : type) : list A → list A → list A =
  elim [
  | nil → λ ys → ys
  | cons x (xs → ih) → λ ys → cons x (ih ys)
  ]

def append/idn/r (A : type) : (xs : list A) → path _ (append A xs nil) xs =
  elim [
  | nil → refl
  | cons x (xs → ih) → λ i → cons x (ih i)
  ]

def append/ass (A : type)
  : (xs ys zs : list A)
  → path _ (append A xs (append A ys zs)) (append A (append A xs ys) zs)
  =
  elim [
  | nil → refl
  | cons x (xs → xs/ih) →
    λ ys zs i → cons x (xs/ih ys zs i)
  ]
