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

; somebody oughta check this is an equivalence!

let s3-to-join (d : s3) : join =
  let face/k01 : [i j m] join [
    | i=1 → push base base m
    | j=0 → weak-connection/and join (λ n → push base base n) i m
    | j=1 → weak-connection/and join (λ n → push base base n) i m
    | m=0 → inl base
    | m=1 → push (loop j) base i
    ]
    =
    λ i j m →
      comp 1 i (push base base m) [
      | j=0 → λ i → weak-connection/and join (λ n → push base base n) i m
      | j=1 → λ i → weak-connection/and join (λ n → push base base n) i m
      | m=0 → λ _ → inl base
      | m=1 → λ i → push (loop j) base i
      ]
 in
  elim d [
  | base → inl base
  | cube i j k →
    comp 1 0 (push (loop j) (loop k) i) [
    | i=0 → λ m → face/k01 0 j m
    | i=1 → λ m → push base (loop k) m
    | j=0 → λ m → weak-connection/and join (λ n → push base (loop k) n) i m
    | j=1 → λ m → weak-connection/and join (λ n → push base (loop k) n) i m
    | k=0 → λ m → face/k01 i j m
    | k=1 → λ m → face/k01 i j m
    ]
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
  | loop i → λ j → join-to-s3/push/loop b i j
  ]

let join-to-s3 (c : join) : s3 =
  elim c [
  | inl a → base
  | inr b → base
  | push a b i → join-to-s3/push a b i
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
