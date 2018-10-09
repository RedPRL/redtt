import path
import pointed
import nat
import int
import s1
import omega1s1
import s2
import s3-to-join

-- from https://github.com/mortberg/cubicaltt/blob/pi4s3/examples/problem.ctt

let pΩ² (pA : ptype) : ptype = pΩ (pΩ pA)
let pΩ³ (pA : ptype) : ptype = pΩ (pΩ² pA)

let pΩ³/reflmap (pA : ptype) (B : type) (f : pA.fst → B)
  : pmap (pΩ³ pA) (pΩ³ (B , f (pA.snd)))
  =
  ( λ c i j k → f (c i j k)
  , refl
  )

let ps2 : ptype = (s2, base)
let ps3 : ptype = (s3, base)
let pjoin : ptype = (join s1 s1, inl base)

let test0-2 : pΩ³ ps3 .fst =
  λ i j k → cube i j k

let f3 : pΩ³ ps3 .fst → pΩ³ pjoin .fst =
  pΩ³/reflmap ps3 (join s1 s1) s3→join .fst

let test0-3 : pΩ³ pjoin .fst = f3 test0-2

let f4 : pΩ³ pjoin .fst → pΩ³ ps2 .fst =
  pΩ³/reflmap pjoin s2 join→s2 .fst

let test0-4 : pΩ³ ps2 .fst = f4 test0-3

let innerpath (i j : dim) : s1 =
  coe 0 1 base in λ k → hopf (test0-4 i j k)

--let problem : path int (pos zero) (pos zero) =
--  λ i → coe 0 1 (pos zero) in λ j → s1-univ-cover (innerpath i j)
