import path
import s1
import s2

data s3 where
| base
| cube @ i j k [
  | i=0 → base
  | i=1 → base
  | j=0 → base
  | j=1 → base
  | k=0 → base
  | k=1 → base
  ]

data join where
| inl [a : s1]
| inr [b : s1]
| push [a : s1] [b : s1] @ i [
  | i=0 → inl a
  | i=1 → inr b
  ]

; forward map

; pseudo-connection
let s3-to-join/cnx (b : s1) (i m : dim) : join =
  comp 0 i (inl base) [
  | m=0 → refl
  | m=1 → λ i → push base b i
  ]

let s3-to-join/k01 : [i j m] join [
  | i=1 → s3-to-join/cnx base 1 m
  | j=0 → s3-to-join/cnx base i m
  | j=1 → s3-to-join/cnx base i m
  | m=0 → inl base
  | m=1 → push (loop j) base i
  ]
  =
  λ i j m →
    comp 1 i (s3-to-join/cnx base 1 m) [
    | j=0 → λ i → s3-to-join/cnx base i m
    | j=1 → λ i → s3-to-join/cnx base i m
    | m=0 → λ _ → inl base
    | m=1 → λ i → push (loop j) base i
    ]

let s3-to-join/cube/filler (i j k x : dim) : join =
  comp 1 x (push (loop j) (loop k) i) [
  | i=0 → λ m → s3-to-join/k01 0 j m
  | i=1 → λ m → s3-to-join/cnx (loop k) 1 m
  | j=0 → λ m → s3-to-join/cnx (loop k) i m
  | j=1 → λ m → s3-to-join/cnx (loop k) i m
  | k=0 → λ m → s3-to-join/k01 i j m
  | k=1 → λ m → s3-to-join/k01 i j m
  ]

let s3-to-join (d : s3) : join =
  elim d [
  | base → inl base
  | cube i j k → s3-to-join/cube/filler i j k 0
  ]

; inverse map

let join-to-s3/push/loop (b : s1)
  : [i j] s3 [ i=0 → base | i=1 → base | j=0 → base | j=1 → base ]
  =
  elim b [
  | base → λ i j → base
  | loop k → λ i j → cube i j k
  ]

let join-to-s3/push (a b : s1) : Path s3 base base =
  elim a [
  | base → λ _ → base
  | loop j → λ i → join-to-s3/push/loop b i j
  ]

let join-to-s3 (c : join) : s3 =
  elim c [
  | inl a → base
  | inr b → base
  | push a b i → join-to-s3/push a b i
  ]

; join-s3-join inverse homotopy

let join-s3-join/inl (a : s1) : Path join (inl base) (inl a) =
  elim a [
  | base → refl
  | loop j → λ x → s3-to-join/k01 0 j x
  ]

let join-s3-join/push/loop (b : s1) : [i j x] join [
  | i=0 → s3-to-join/k01 0 j x
  | i=1 → s3-to-join/cnx b 1 x
  | j=0 → s3-to-join/cnx b i x
  | j=1 → s3-to-join/cnx b i x
  | x=0 → s3-to-join (join-to-s3/push/loop b i j)
  | x=1 → push (loop j) b i
  ]
  =
  elim b [
  | base → λ i j x → s3-to-join/k01 i j x
  | loop k → λ i j x → s3-to-join/cube/filler i j k x
  ]

let join-s3-join/push (a b : s1) : [i x] join [
  | i=0 → join-s3-join/inl a x
  | i=1 → s3-to-join/cnx b 1 x
  | x=0 → s3-to-join (join-to-s3/push a b i)
  | x=1 → push a b i
  ]
  =
  elim a [
  | base → λ i x → s3-to-join/cnx b i x
  | loop j → λ i x → join-s3-join/push/loop b i j x
  ]

let join-s3-join (c : join) : Path join (s3-to-join (join-to-s3 c)) c =
  elim c [
  | inl a → λ x → join-s3-join/inl a x
  | inr b → λ x → s3-to-join/cnx b 1 x
  | push a b i → λ x → join-s3-join/push a b i x
  ]

; adapted from "alpha" in cubicaltt:
; https://github.com/mortberg/cubicaltt/blob/d3afca5a744a96de4831610e76d6c4b629478362/examples/brunerie2.ctt#L322

let s2/merid (a : s1) : Path s2 base base =
  elim a [
  | base → λ _ → base
  | loop i → λ j → surf i j
  ]

let join-to-s2 (c : join) : s2 =
  elim c [
  | inl a → base
  | inr b → base
  | push a b i → trans s2 (s2/merid a) (s2/merid b) i
  ]
