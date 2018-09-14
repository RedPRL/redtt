import bool
import s1
import isotoequiv

let not/equiv : equiv bool bool
  = iso→equiv _ _ (not, (not, (not∘not/id/pt, not∘not/id/pt)))

let not/path : path^1 type bool bool
  = ua _ _ not/equiv

let moebius-boundary/fiber (x : s1) : type =
  elim x [
  | base → bool
  | loop i → not/path i
  ]

let moebius-boundary : type = (x : s1) × moebius-boundary/fiber x

let moebius-boundary→s1' (x : s1) : moebius-boundary/fiber x → s1 =
  let eta-expand (i : dim) (y : bool) : s1 =
    elim y [ tt → loop i | ff → base ]
  in
  let commuting (y : bool)
    : path _ (eta-expand 1 (not y)) (eta-expand 0 y)
    = elim y [ tt → refl | ff → refl ]
  in
  elim x [
  | base → eta-expand 0
  | loop i → λ y →
    let z : bool = coe i 0 y in not/path in
    comp 0 1 (eta-expand i z) [i=0 → refl | i=1 → commuting y]
  ]

let moebius-boundary→s1 (x : moebius-boundary) : s1 =
  moebius-boundary→s1' (x .fst) (x .snd)

let s1→moebius-boundary (x : s1) : moebius-boundary =
  elim x [
  | base → (base, tt)
  | loop i →
      let loop-path (b : bool)
        : path moebius-boundary (base, b) (base, not b) =
        λ i → (loop i , `(vin i b (not b)))
      in
      comp 0 1 (loop-path tt i) [i=0 → refl | i=1 → loop-path ff]
  ]

let s1→moebius-boundary→s1
  : path s1 (moebius-boundary→s1 (s1→moebius-boundary base)) base =
  refl

-- there is an invalid fhcom in the middle?!
-- ... (fhcom 0 1 (loop x) [x=0 <x1> base]) ...
let test : dim → s1 =
  λ i → moebius-boundary→s1 (s1→moebius-boundary (loop i))
normalize test

/-
let double : s1 → s1 = λ x → s1→moebius-boundary x .fst

import omega1s1

let test0 : path int (winding (λ i → double (loopn (pos (suc zero)) i))) (pos (suc (suc zero))) = refl
-/
