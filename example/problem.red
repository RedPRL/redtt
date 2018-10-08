import path
import pointed
import nat
import int
import s1
import omega1s1
import s2
import s3-to-join

-- from https://github.com/mortberg/cubicaltt/blob/pi4s3/examples/problem.ctt

def pΩ² (pA : ptype) : ptype = pΩ (pΩ pA)
def pΩ³ (pA : ptype) : ptype = pΩ (pΩ² pA)

def pΩ³/reflmap (pA : ptype) (B : type) (f : pA.fst → B)
  : pmap (pΩ³ pA) (pΩ³ (B , f (pA.snd)))
  =
  ( λ c i j k → f (c i j k)
  , refl
  )

def ps2 : ptype = (s2, base)
def ps3 : ptype = (s3, base)
def pjoin : ptype = (join s1 s1, inl base)

def test0-2 : pΩ³ ps3 .fst =
  λ i j k → cube i j k

def f3 : pΩ³ ps3 .fst → pΩ³ pjoin .fst =
  pΩ³/reflmap ps3 (join s1 s1) s3→join .fst

def test0-3 : pΩ³ pjoin .fst = f3 test0-2

def f4 : pΩ³ pjoin .fst → pΩ³ ps2 .fst =
  pΩ³/reflmap pjoin s2 join→s2 .fst

def test0-4 : pΩ³ ps2 .fst = f4 test0-3

def innerpath (i j : dim) : s1 =
  coe 0 1 base in λ k → hopf (test0-4 i j k)

--let problem : path int (pos zero) (pos zero) =
--  λ i → coe 0 1 (pos zero) in λ j → s1-univ-cover (innerpath i j)
