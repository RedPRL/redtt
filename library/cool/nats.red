import prelude
import data.bool
import data.nat
import basics.isotoequiv

data binnat where
| nil                -- 0
| cons1 (x : binnat) -- 2n + 1
| cons2 (x : binnat) -- 2n + 2

def double/nat : nat → nat =
  elim [
  | zero → zero
  | suc (_ → ih) → suc (suc ih)
  ]

def binnat→nat : binnat → nat =
  elim [
  | nil → zero
  | cons1 (_ → ih) → suc (double/nat ih)
  | cons2 (_ → ih) → suc (suc (double/nat ih))
  ]

def suc/binnat : binnat → binnat =
  elim [
  | nil → cons1 nil
  | cons1 n → cons2 n
  | cons2 (_ → ih) → cons1 ih
  ]

def nat→binnat : nat → binnat =
  elim [
  | zero → nil
  | suc (_ → ih) → suc/binnat ih
  ]

def binnat→nat-suc (n : binnat)
  : path _ (binnat→nat (suc/binnat n)) (suc (binnat→nat n)) =
  elim n [
  | nil → refl
  | cons1 _ → refl
  | cons2 (_ → ih) → λ i → suc (double/nat (ih i))
  ]

def nat→binnat→nat (n : nat)
  : path _ (binnat→nat (nat→binnat n)) n =
  elim n [
  | zero → refl
  | suc (n → ih) → trans nat (binnat→nat-suc (nat→binnat n)) (λ i → suc (ih i))
  ]

def suc-nat→binnat-double (n : nat)
  : path binnat (suc/binnat (nat→binnat (double/nat n))) (cons1 (nat→binnat n)) =
  elim n [
  | zero → refl
  | suc (_ → ih) → λ i → suc/binnat (suc/binnat (ih i))
  ]

def binnat→nat→binnat (n : binnat)
  : path _ (nat→binnat (binnat→nat n)) n =
  elim n [
  | nil → refl
  | cons1 (n → ih) → trans binnat (suc-nat→binnat-double (binnat→nat n)) (λ i → cons1 (ih i))
  | cons2 (n → ih) → trans binnat (λ i → suc/binnat (suc-nat→binnat-double (binnat→nat n) i)) (λ i → cons2 (ih i))
  ]

def nat≃binnat : equiv nat binnat =
  iso→equiv _ _
    (nat→binnat,
     binnat→nat,
     binnat→nat→binnat,
     nat→binnat→nat)

def n≈bn : path^1 type nat binnat = ua _ _ nat≃binnat



-- We can transport functions between these two types, and run them!
-- From nat → nat → nat to binnat → binnat → binnat...

def plus/binnat : binnat → binnat → binnat =
  coe 0 1 plus in λ i → n≈bn i → n≈bn i → n≈bn i
--                i=0:  nat    → nat    → nat
--                i=1:  binnat → binnat → binnat

-- plus and plus/binnat are equal, modulo n≈bn
def plus/n≈bn : pathd^1 (λ i → n≈bn i → n≈bn i → n≈bn i) plus plus/binnat =
  λ i → coe 0 i plus in λ i → n≈bn i → n≈bn i → n≈bn i

def test : binnat = plus/binnat (cons1 nil) (cons1 nil)
meta ⦉ print normalize test ⦊

-- From binnat → bool to nat → bool...

def oddq : binnat → bool =
  elim [
  | nil → ff
  | cons1 _ → tt
  | cons2 _ → ff
  ]

def oddq/n≈bn (i : 𝕀) : (n≈bn i) → bool =
  coe 1 i oddq in λ i → (n≈bn i) → bool

def oddq/nat : nat → bool = oddq/n≈bn 0

-- nat and binnat are equal implementations of the 'nat' interface.

def impl : type^1 = (A : type) × A × (A → A)
def impl/nat : impl = (nat, zero, λ n → suc n)
def impl/binnat : impl = (binnat, nil, suc/binnat)

def impl/n≈bn : path^1 impl impl/nat impl/binnat =
  λ i →
  (n≈bn i,
   coe 0 i zero in n≈bn,
   -- MORTAL
   λ v → let v' : n≈bn i = (suc v, suc/binnat (v .vproj)) in v'
  )

-- We can also transport proofs *about* these functions.

def oddq/suc : (n : binnat) → path bool (oddq n) (not (oddq (suc/binnat n))) =
  λ * → refl

def oddq/nat/suc : (n : nat) → path bool (oddq/nat n) (not (oddq/nat (suc n))) =
  coe 1 0 oddq/suc
  in λ i → (n : n≈bn i) →
    path bool (oddq/n≈bn i n) (not (oddq/n≈bn i (impl/n≈bn i .snd.snd n)))

def oddq/nat/direct : nat → bool =
  elim [
  | zero → ff
  | suc (_ → ih) → not ih
  ]

/- MORTAL
def oddq/n≈bn : (n : nat) → path bool (oddq/nat n) (oddq/nat/direct n) =
  let pf : (n : nat) → path _ (suc/binnat (nat→binnat n)) (nat→binnat (suc n)) =
    λ * → refl
  in
  elim [
  | zero → refl
  | suc (n → ih) → λ i → not (trans bool (λ i → oddq (pf n i)) ih i)
  ]
-/
