import bool
import s1
import isotoequiv

let not/equiv : equiv bool bool =
  iso→equiv _ _ (not, (not, (not∘not/id/pt, not∘not/id/pt)))

let not/path : path^1 type bool bool =
  ua _ _ not/equiv

let moebius-boundary/fiber (x : s1) : type =
  elim x [
  | base → bool
  | loop i → not/path i
  ]

let moebius-boundary : type = (x : s1) × moebius-boundary/fiber x

let moebius-boundary→s1/loop-base (i : dim) (y : bool) : s1 =
  elim y [ tt → loop i | ff → base ]

let moebius-boundary→s1/commuting (y : bool) :
  path _
    (moebius-boundary→s1/loop-base 0 y)
    (moebius-boundary→s1/loop-base 1 (coe 0 1 y in not/path))
  =
  elim y [ tt → refl | ff → refl ]

let moebius-boundary→s1/loop/filler (i j : dim) (y : not/path i) : s1 =
  let z : bool = coe i 1 y in not/path
  in
  comp 1 j (moebius-boundary→s1/loop-base i z) [
  | i=0 → moebius-boundary→s1/commuting y
  | i=1 → refl
  ]

let moebius-boundary→s1' (x : s1) : moebius-boundary/fiber x → s1 =
  elim x [
  | base → moebius-boundary→s1/loop-base 0
  | loop i → moebius-boundary→s1/loop/filler i 0
  ]

let moebius-boundary→s1 (x : moebius-boundary) : s1 =
  moebius-boundary→s1' (x .fst) (x .snd)

let s1→moebius-boundary/base : moebius-boundary =
  (base, ff)

let loop-path (b : bool) :
  path moebius-boundary (base, b) (base, not b) =
  λ i → (loop i , `(vin i b (not b)))

let s1→moebius-boundary/loop/filler (i j : dim) : moebius-boundary =
  comp 0 j (loop-path ff i) [i=0 → refl | i=1 → loop-path tt]

let s1→moebius-boundary (x : s1) : moebius-boundary =
  elim x [
  | base → s1→moebius-boundary/base
  | loop i → s1→moebius-boundary/loop/filler i 1
  ]

let s1→moebius-boundary→s1/base :
  path s1 (moebius-boundary→s1 (s1→moebius-boundary base)) base =
  refl

opaque let s1→moebius-boundary→s1/loop :
  [i j] s1 [
  | ∂[i] → base
  | j=0 → moebius-boundary→s1 (s1→moebius-boundary/loop/filler i 1)
  | j=1 → loop i
  ]
  =
  λ i j →
    comp 0 1 (moebius-boundary→s1/loop/filler i j (loop-path ff i .snd)) [
    | i=0 → refl
    | i=1 k → moebius-boundary→s1/loop/filler k j (loop-path tt k .snd)
    | j=0 k → moebius-boundary→s1 (s1→moebius-boundary/loop/filler i k)
    | j=1 → refl
    ]

quit

let s1→moebius-boundary→s1 (x : s1) :
  path s1 (moebius-boundary→s1 (s1→moebius-boundary x)) x =
  elim x [
  | base → refl
  | loop i → λ j → s1→moebius-boundary→s1/loop i j
  ]

quit

-- there is an invalid fhcom in the middle?!
-- ... (fhcom 0 1 (loop x) [x=0 <x1> base]) ...
let test : dim → moebius-boundary =
  λ i → s1→moebius-boundary (loop i)
--normalize test

-- there is an invalid fhcom in the middle?!
-- ... (fhcom 0 1 (loop x) [x=0 <x1> base]) ...
let test1 : dim → s1 =
  λ i → moebius-boundary→s1 (s1→moebius-boundary (loop i))
-- normalize test1

/-
let double : s1 → s1 = λ x → s1→moebius-boundary x .fst

import omega1s1

let test0 : path int (winding (λ i → double (loopn (pos (suc zero)) i))) (pos (suc (suc zero))) = refl
-/
