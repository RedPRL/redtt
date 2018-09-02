import path
import s1
import s2

data s3 where
| base
| cube @ i j k [
  | i=0 ⇒ base
  | i=1 ⇒ base
  | j=0 ⇒ base
  | j=1 ⇒ base
  | k=0 ⇒ base
  | k=1 ⇒ base
  ]

data join where
| inl [a : s1]
| inr [b : s1]
| push [a : s1] [b : s1] @ i [
  | i=0 ⇒ inl a
  | i=1 ⇒ inr b
  ]

; adapted from "e" in cubicaltt:
; https://github.com/mortberg/cubicaltt/blob/d3afca5a744a96de4831610e76d6c4b629478362/examples/brunerie2.ctt#L298

let s3-to-join (d : s3) : join =
  ; need to make the faces of this all (inl base)
  let step0 : [i j k] join [
    | i=0 ⇒ inl (loop j)
    | i=1 ⇒ inr (loop k)
    | j=0 ⇒ push base (loop k) i
    | j=1 ⇒ push base (loop k) i
    | k=0 ⇒ push (loop j) base i
    | k=1 ⇒ push (loop j) base i
    ]
    =
    λ i j k →
      push (loop j) (loop k) i
  in
  ; like a connection, but we don't need to know all the faces
  let filler1 : [j m] s1 [
    | m=0 ⇒ loop j
    | m=1 ⇒ base
    ]
    =
    λ j m →
      comp 0 j base [
      | m=0 ⇒ λ j → loop j
      | m=1 ⇒ λ _ → base
      ]
  in
  ; get rid of loops
  let step1 : [i j k] join [
    | i=0 ⇒ inl base
    | i=1 ⇒ inr base
    | j=0 ⇒ push base base i
    | j=1 ⇒ push base base i
    | k=0 ⇒ push base base i
    | k=1 ⇒ push base base i
    ]
    =
    λ i j k →
      comp 0 1 (step0 i j k) [
      | i=0 ⇒ λ m → inl (filler1 j m)
      | i=1 ⇒ λ m → inr (filler1 k m)
      | j=0 ⇒ λ m → push (filler1 0 m) (filler1 k m) i
      | j=1 ⇒ λ m → push (filler1 1 m) (filler1 k m) i
      | k=0 ⇒ λ m → push (filler1 j m) (filler1 0 m) i
      | k=1 ⇒ λ m → push (filler1 j m) (filler1 1 m) i
      ]
  in
  ; like a connection, but we don't need to know all the faces
  let filler2 : [i m] join [
    | m=0 ⇒ push base base i
    | m=1 ⇒ inl base
    ]
    =
    λ i m →
      comp 0 i (inl base) [
      | m=0 ⇒ λ i → push base base i
      | m=1 ⇒ λ _ → inl base
      ]
  in
  ; get rid of push
  let step2 : [i j k] join [
    | i=0 ⇒ inl base
    | i=1 ⇒ inl base
    | j=0 ⇒ inl base
    | j=1 ⇒ inl base
    | k=0 ⇒ inl base
    | k=1 ⇒ inl base
    ]
    =
    λ i j k →
      comp 0 1 (step1 i j k) [
      | i=0 ⇒ λ _ → inl base
      | i=1 ⇒ λ m → filler2 1 m
      | j=0 ⇒ λ m → filler2 i m
      | j=1 ⇒ λ m → filler2 i m
      | k=0 ⇒ λ m → filler2 i m
      | k=1 ⇒ λ m → filler2 i m
      ]
  in
  elim d [
  | base ⇒ inl base
  | cube i j k ⇒ step2 i j k
  ]

; inverse map

let join-to-s3/push/loop (b : s1)
  : [i j] s3 [ i=0 ⇒ base | i=1 ⇒ base | j=0 ⇒ base | j=1 ⇒ base ]
  =
  elim b [
  | base ⇒ λ i j → base
  | loop k ⇒ λ i j → cube i j k
  ]

let join-to-s3/push (a, b : s1) : Path s3 base base =
  elim a [
  | base ⇒ λ _ → base
  | loop i ⇒ λ j → join-to-s3/push/loop b i j
  ]

let join-to-s3 (c : join) : s3 =
  elim c [
  | inl a ⇒ base
  | inr b ⇒ base
  | push a b i ⇒ join-to-s3/push a b i
  ]

; adapted from "alpha" in cubicaltt:
; https://github.com/mortberg/cubicaltt/blob/d3afca5a744a96de4831610e76d6c4b629478362/examples/brunerie2.ctt#L322

let s2/merid (a : s1) : Path s2 base base =
  elim a [
  | base ⇒ λ _ → base
  | loop i ⇒ λ j → surf i j
  ]

let join-to-s2 (c : join) : s2 =
  elim c [
  | inl a ⇒ base
  | inr b ⇒ base
  | push a b i ⇒ trans s2 (s2/merid a) (s2/merid b) i
  ]
