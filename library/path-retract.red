import path
import J
import equivalence
import isotoequiv
import retract

-- a retract of the path family is an equivalence

-- a path retract always preserves refl, but you might have a more efficient proof
def path-retract/preserves-refl→equiv (A : type) (R : A → A → type)
  (ret : (x y : A) → retract (R x y) (path A x y)) (a b : A)
  (preserves-refl : path _ (ret a a .fst (ret a a .snd .fst refl)) refl)
  : equiv (R a b) (path A a b)
  =
  let s (x y : A) : R x y → path A x y = ret x y .fst in
  let r (x y : A) : path A x y → R x y = ret x y .snd .fst in
  let α (x y : A) : (t : R x y) → path (R x y) (r x y (s x y t)) t =
    ret x y .snd .snd
  in
  iso→equiv (R a b) (path A a b)
    ( s a b
    , r a b
    , λ p → J A p (λ q → path _ (ret a (q 1) .fst (ret a (q 1) .snd .fst q)) q) preserves-refl
    , α a b
    )

def path-retract/equiv (A : type) (R : A → A → type)
  (ret : (x y : A) → retract (R x y) (path A x y)) (a b : A)
  : equiv (R a b) (path A a b)
  =
  path-retract/preserves-refl→equiv A R ret a b
    (path-retract/preserves-refl A R ret a)
