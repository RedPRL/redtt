import prelude
import data.bool
import data.nat
import data.s1
import data.susp
import basics.isotoequiv

def sphere1 : type = sphere (suc zero)

def sphere1→s1 : sphere1 → s1 =
  elim [
  | north → base
  | south → base
  | merid b i →
    elim b in λ _ → path s1 base base [
    | ff → λ j → loop j
    | tt → refl
    ] i
  ]

def s1→sphere1 : s1 → sphere1 =
  elim [
  | base → north
  | loop i → comp 1 0 (merid ff i) [i=0 → refl | i=1 j → merid tt j]
  ]

def sphere1→s1→sphere1 : (s : sphere1) → path _ (s1→sphere1 (sphere1→s1 s)) s =
  elim [
  | north → refl
  | south → λ j → merid tt j
  | merid b i →
    let mot (b : bool) : type =
      pathd (λ i → path _ (s1→sphere1 (sphere1→s1 (merid b i))) (merid b i)) refl (λ j → merid tt j)
    in
    elim b in mot [
    | tt → λ i j → weak-connection/and sphere1 (λ n → merid tt n) i j
    | ff → λ i j → comp 1 j (merid ff i) [i=0 → refl | i=1 j → merid tt j]
    ] i
  ]

def s1→sphere1→s1 : (c : s1) → path _ (sphere1→s1 (s1→sphere1 c)) c =
  elim [
  | base → refl
  | loop i → λ j → comp 1 j (loop i) [∂[i] → refl]
  ]

def sphere1→s1/equiv : equiv sphere1 s1 =
  iso→equiv _ _ (sphere1→s1, s1→sphere1, s1→sphere1→s1, sphere1→s1→sphere1)
