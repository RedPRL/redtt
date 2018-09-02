import path
import pointed
import nat
import int
import s1
import omega1s1
import s2
import s3-to-join

; from https://github.com/mortberg/cubicaltt/blob/pi4s3/examples/problem.ctt

let pΩ² (pA : ptype) : ptype = pΩ (pΩ pA)
let pΩ³ (pA : ptype) : ptype = pΩ (pΩ² pA)

let pΩ³/reflmap (pA : ptype) (B : type) (f : (pA.0) → B)
  : pmap (pΩ³ pA) (pΩ³ (B , f (pA.1)))
  =
  ( λ c i j k → f (c i j k)
  , refl
  )

let ps2 : ptype = (s2, base)
let ps3 : ptype = (s3, base)
let pjoin : ptype = (join, inl base)

let test0-2 : pΩ³ ps3 .0 =
  λ i j k → cube i j k

let f3 : pΩ³ ps3 .0 → pΩ³ pjoin .0 =
  pΩ³/reflmap ps3 join s3-to-join .0

let test0-3 : pΩ³ pjoin .0 = f3 test0-2

let f4 : pΩ³ pjoin .0 → pΩ³ ps2 .0 =
  pΩ³/reflmap pjoin s2 join-to-s2 .0

let test0-4 : pΩ³ ps2 .0 = f4 test0-3

; haven't seen this finish checking
;let innerpath (i j : dim) : s1 =
;  coe 0 1 base in λ k → hopf (test0-4 i j k)
