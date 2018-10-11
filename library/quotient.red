import ntype
import truncation
import equivalence
import isotoequiv

data (A : type) (R : A → A → type) ⊢ quotient where
| pt (a : A)
| gl (a b : A) (p : R a b) (i : 𝕀) [
  | i=0 → pt a
  | i=1 → pt b
  ]

def is-compat (A B : type) (R : A → A → type) (f : A → B) : type =
  (a0 a1 : A) → R a0 a1 → path _ (f a0) (f a1)

def prop/ext
  (A B : type)
  (A/prop : is-prop A)
  (B/prop : is-prop B)
  (f : A → B)
  (g : B → A)
  : path^1 type A B
  =
  ua _ _
   (iso→equiv _ _
    (f, g, λ _ → B/prop _ _, λ _ → A/prop _ _))

def trunc/ext
  (A B : type)
  (f : A → B)
  (g : B → A)
  : path^1 type (trunc A) (trunc B)
  =
  prop/ext _ _ (trunc/prop A) (trunc/prop B) (trunc/map _ _ f) (trunc/map _ _ g)


/- This proof is roughly based on Veltri's informal proof in
   http://cs.ioc.ee/~niccolo/splst15.pdf -/

def quotient/weakly-effective
  (A : type) (R : A → A → type)
  (R/refl : (a : A) → R a a)
  (R/symm : (a b : A) → R a b → R b a)
  (R/trans : (a b c : A) → R a b → R b c → R a c)
  : (a b : A)
  → path (quotient A R) (pt a) (pt b)
  → trunc (R a b)
  =
  λ a →
  let f (b : A) : type = trunc (R a b) in
  let f/compat : is-compat^1 _ _ R f =
    λ b0 b1 b01 →
    let g0 (x : R a b0) : R a b1 = R/trans _ _ _ x b01 in
    let g1 (x : R a b1) : R a b0 = R/trans _ _ _ x (R/symm _ _ b01) in
    trunc/ext _ _ g0 g1
  in
  λ b p →
    coe 0 1 (ret (R/refl a)) in λ i →
    elim (p i) [
    | pt b → f b
    | gl b0 b1 b01 i →
      f/compat b0 b1 b01 i
    ]

