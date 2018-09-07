import path
import s1
import s2
import isotoequiv

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
  | m=1 i → push base b i
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
    | j=0 i → s3-to-join/cnx base i m
    | j=1 i → s3-to-join/cnx base i m
    | m=0 → refl
    | m=1 i → push (loop j) base i
    ]

let s3-to-join/cube/filler (i j k m : dim) : join =
  comp 1 m (push (loop j) (loop k) i) [
  | i=0 m → s3-to-join/k01 0 j m
  | i=1 m → s3-to-join/cnx (loop k) 1 m
  | j=0 m → s3-to-join/cnx (loop k) i m
  | j=1 m → s3-to-join/cnx (loop k) i m
  | k=0 m → s3-to-join/k01 i j m
  | k=1 m → s3-to-join/k01 i j m
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
  | loop j → λ m → s3-to-join/k01 0 j m
  ]

let join-s3-join/push/loop (b : s1) : [i j m] join [
  | i=0 → s3-to-join/k01 0 j m
  | i=1 → s3-to-join/cnx b 1 m
  | j=0 → s3-to-join/cnx b i m
  | j=1 → s3-to-join/cnx b i m
  | m=0 → s3-to-join (join-to-s3/push/loop b i j)
  | m=1 → push (loop j) b i
  ]
  =
  elim b [
  | base → λ i j m → s3-to-join/k01 i j m
  | loop k → λ i j m → s3-to-join/cube/filler i j k m
  ]

let join-s3-join/push (a b : s1) : [i m] join [
  | i=0 → join-s3-join/inl a m
  | i=1 → s3-to-join/cnx b 1 m
  | m=0 → s3-to-join (join-to-s3/push a b i)
  | m=1 → push a b i
  ]
  =
  elim a [
  | base → λ i m → s3-to-join/cnx b i m
  | loop j → λ i m → join-s3-join/push/loop b i j m
  ]

let join-s3-join (c : join) : Path join (s3-to-join (join-to-s3 c)) c =
  elim c [
  | inl a → λ m → join-s3-join/inl a m
  | inr b → λ m → s3-to-join/cnx b 1 m
  | push a b i → λ m → join-s3-join/push a b i m
  ]

; s3-join-s3 inverse homotopy

let s3-join-s3 (d : s3) : Path s3 (join-to-s3 (s3-to-join d)) d =
  elim d [
  | base → refl
  | cube i j k → λ x →
    let cnx/image : (i m : dim) → s3 =
      λ i m → comp 0 i base [ m=0 → refl | m=1 → refl ]
    in
    let cnx/filler : (i m x : dim) → s3 =
      λ i m x →
        comp 0 i base
        [ m=0 → refl
        | m=1 → refl
        | x=0 → λ i → cnx/image i m
        | x=1 → refl
        ]
    in
    let k01/image : (i m : dim) → s3 =
      λ i m →
        comp 1 i (cnx/image 1 m) [
        | j=0 → λ i → cnx/image i m
        | j=1 → λ i → cnx/image i m
        | m=0 → refl
        | m=1 → refl
        ]
    in
    let k01/filler : (i m x : dim) → s3 =
      λ i m x →
       comp 1 i (cnx/filler 1 m x) [
       | j=0 → λ i → cnx/filler i m x
       | j=1 → λ i → cnx/filler i m x
       | m=0 → refl
       | m=1 → refl
       | x=0 → λ i → k01/image i m
       | x=1 → refl
       ]
    in
    comp 1 0 (cube i j k) [
    | i=0 → λ m → k01/filler 0 m x
    | i=1 → λ m → cnx/filler 1 m x
    | j=0 → λ m → cnx/filler i m x
    | j=1 → λ m → cnx/filler i m x
    | k=0 → λ m → k01/filler i m x
    | k=1 → λ m → k01/filler i m x
    | x=0 → λ m → join-to-s3 (s3-to-join/cube/filler i j k m)
    | x=1 → refl
    ]
  ]

; equivalence

let s3-to-join/iso : Iso s3 join =
  (s3-to-join, join-to-s3, join-s3-join, s3-join-s3)

let s3-to-join/equiv : Equiv s3 join =
  Iso/Equiv s3 join s3-to-join/iso

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
