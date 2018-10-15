import path
import s1
import s2
import join
import equivalence
import isotoequiv

-- forward map

-- pseudo-connection
def s3→join/cnx (b : s1) (i m : 𝕀) : join s1 s1 =
  comp 0 i (inl base) [
  | m=0 → refl
  | m=1 i → push base b i
  ]

def s3→join/k01 :
  [i j m] join s1 s1 [
  | i=1 → s3→join/cnx base 1 m
  | ∂[j] → s3→join/cnx base i m
  | m=0 → inl base
  | m=1 → push (loop j) base i
  ]
  =
  λ i j m →
    comp 1 i (s3→join/cnx base 1 m) [
    | ∂[j] i → s3→join/cnx base i m
    | m=0 → refl
    | m=1 i → push (loop j) base i
    ]

def s3→join/cube/filler (i j k m : 𝕀) : join s1 s1 =
  comp 1 m (push (loop j) (loop k) i) [
  | i=1 | ∂[j] → s3→join/cnx (loop k) i
  | (i=0 | ∂[k]) m → s3→join/k01 i j m
  ]

def s3→join : s3 → join s1 s1 =
  elim [
  | base → inl base
  | cube i j k → s3→join/cube/filler i j k 0
  ]

-- inverse map

def join→s3/push/loop : s1 → [i j] s3 [ ∂[i j] → base ] =
  elim [
  | base → refl
  | loop k → λ i j → cube i j k
  ]

def join→s3/push (a b : s1) : path s3 base base =
  elim a [
  | base → refl
  | loop j → λ i → join→s3/push/loop b i j
  ]

def join→s3 : join s1 s1 → s3 =
  elim [
  | push a b i → join→s3/push a b i
  | * → base
  ]

-- join-s3-join inverse homotopy

def join-s3-join/inl : (a : s1) → path (join s1 s1) (inl base) (inl a) =
  elim [
  | base → refl
  | loop j → λ m → s3→join/k01 0 j m
  ]

def join-s3-join/push/loop
  : (b : s1) →
    [i j m] join s1 s1 [
    | i=0 → s3→join/k01 0 j m
    | i=1 | ∂[j] → s3→join/cnx b i m
    | m=0 → s3→join (join→s3/push/loop b i j)
    | m=1 → push (loop j) b i
    ]
  =
  elim [
  | base → λ i j m → s3→join/k01 i j m
  | loop k → λ i j m → s3→join/cube/filler i j k m
  ]

def join-s3-join/push
  : (a b : s1) →
    [i m] join s1 s1 [
    | i=0 → join-s3-join/inl a m
    | i=1 → s3→join/cnx b 1 m
    | m=0 → s3→join (join→s3/push a b i)
    | m=1 → push a b i
    ]
  =
  elim [
  | base → λ b i m → s3→join/cnx b i m
  | loop j → λ b i m → join-s3-join/push/loop b i j m
  ]

def join-s3-join : (c : join s1 s1) → path _ (s3→join (join→s3 c)) c =
  elim [
  | inl a → λ m → join-s3-join/inl a m
  | inr b → λ m → s3→join/cnx b 1 m
  | push a b i → λ m → join-s3-join/push a b i m
  ]

-- s3-join-s3 inverse homotopy

def s3-join-s3 : (d : s3) → path _ (join→s3 (s3→join d)) d =
  elim [
  | base → refl
  | cube i j k → λ x →
    let cnx/filler (i m x : 𝕀) : s3 =
      comp 0 i base [∂[m] | x=1 → refl]
    in
    let k01/filler (i m x : 𝕀) : s3 =
      comp 1 i (cnx/filler 1 m x) [
      | ∂[j] i → cnx/filler i m x
      | ∂[m] | x=1 → refl
      ]
    in
    comp 1 0 (cube i j k) [
    | (i=1 | ∂[j]) m → cnx/filler i m x
    | (i=0 | ∂[k]) m → k01/filler i m x
    | x=0 m → join→s3 (s3→join/cube/filler i j k m)
    | x=1 → refl
    ]
  ]

-- equivalence

def s3→join/iso : iso s3 (join s1 s1) =
  (s3→join, join→s3, join-s3-join, s3-join-s3)

def s3→join/equiv : equiv s3 (join s1 s1) =
  iso→equiv s3 (join s1 s1) s3→join/iso

-- adapted from "alpha" in cubicaltt:
-- https://github.com/mortberg/cubicaltt/blob/d3afca5a744a96de4831610e76d6c4b629478362/examples/brunerie2.ctt#L322

def s2/merid : s1 → path s2 base base =
  elim [
  | base → refl
  | loop i → λ j → surf i j
  ]

def join→s2 : join s1 s1 → s2 =
  elim [
  | push a b i → trans s2 (s2/merid a) (s2/merid b) i
  | * → base
  ]
