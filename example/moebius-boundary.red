import bool
import s1
import isotoequiv

let not/equiv : equiv bool bool =
  iso→equiv _ _ (not, (not, (not∘not/id/pt, not∘not/id/pt)))

let not/path : path^1 type bool bool =
  ua _ _ not/equiv

let moebius-boundary/fiber : s1 → type =
  elim [
  | base → bool
  | loop i → not/path i
  ]

let moebius-boundary : type = (x : s1) × moebius-boundary/fiber x

let loop-or-base (i : dim) : bool → s1 =
  elim [ tt → loop i | ff → base ]

let loop-or-base/commuting :
  (y : bool) →
  path _
    (loop-or-base 0 y)
    (loop-or-base 0 (coe 0 1 y in not/path))
  =
  elim [ tt → refl | ff → refl ]

let moebius-boundary→s1/loop/filler (i j : dim) (y : not/path i) : s1 =
  let z : bool = coe i 1 y in not/path
  in
  comp 1 j (loop-or-base i z) [
  | i=0 → loop-or-base/commuting y
  | i=1 → refl
  ]

let moebius-boundary→s1 : moebius-boundary → s1 =
  λ [,] →
  elim [
  | base → elim [ tt → base | ff → base ]
  | loop i → moebius-boundary→s1/loop/filler i 0
  ]

let s1→moebius-boundary/base : moebius-boundary =
  (base, ff)

let loop-path (b : bool) :
  path moebius-boundary (base, b) (base, not b) =
  λ i → (loop i , `(vin i b (not b)))

let s1→moebius-boundary/loop/filler (i j : dim) : moebius-boundary =
  comp 0 j (loop-path ff i) [i=0 → refl | i=1 → loop-path tt]

let s1→moebius-boundary : s1 → moebius-boundary =
  elim [
  | base → s1→moebius-boundary/base
  | loop i → s1→moebius-boundary/loop/filler i 1
  ]

/-
let moebius-boundary→s1→moebius-boundary :
  (x : moebius-boundary) → path _ (s1→moebius-boundary (moebius-boundary→s1 x)) x
  =
  λ [,] →
  elim [
  | base →
    elim [
    | tt → loop-path ff
    | ff → refl
    ]
  | loop i → ?
  ]

quit
-/

let s1→moebius-boundary→s1/loop :
  [i j] s1 [
  | ∂[i] → base
  | j=0 → moebius-boundary→s1 (s1→moebius-boundary (loop i))
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

/-
  This will force re-typechecking `box`, but why?
-/
let s1→moebius-boundary→s1 :
  (x : s1) → path s1 (moebius-boundary→s1 (s1→moebius-boundary x)) x
  =
  elim [
  | base → refl
  | loop i → λ j → s1→moebius-boundary→s1/loop i j
  ]

/-
let double : s1 → s1 = λ x → s1→moebius-boundary x .fst

import omega1s1

let test0 :
  path int
    (winding (λ i → double (loopn (pos (suc zero)) i)))
    (pos (suc (suc zero))) =
  refl
-/
