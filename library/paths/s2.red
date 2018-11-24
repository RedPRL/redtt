import prelude
import data.s2
import basics.isotoequiv
import paths.equivalence

-- a calculation of the loop space of the 2-sphere, based on
-- https://egbertrijke.com/2016/09/28/the-loop-space-of-the-2-sphere/

-- loop space of s2
data os2 where
| obase
| oloop (y : os2) (i : 𝕀) [∂[i] → y]

-- I. the loop of automorphisms of os2

-- it would probably be more efficient to define this directly,
-- but we don't need it
def oloop-equiv : path (equiv os2 os2) (id-equiv/weak-connection os2) (id-equiv/weak-connection os2) =
  λ i →
  ( λ o → oloop o i
  , prop→prop-over
    (λ j → is-equiv os2 os2 (λ o → oloop o j))
    (is-equiv/prop/direct os2 os2 (λ o → o))
    (id-equiv/weak-connection os2 .snd)
    (id-equiv/weak-connection os2 .snd)
    i
  )

-- incidentally, onegloop o is homotopic to symm (λ i → oloop o i)
def onegloop (o : os2) : path os2 o o =
  λ i → oloop-equiv i .snd o .fst .fst

def oloop-onegloop (o : os2)
  : pathd (λ i → path os2 (oloop (onegloop o i) i) o) refl refl
  =
  λ i → oloop-equiv i .snd o .fst .snd

-- II. universal cover over s2

def s2/code/surf/filler (m i j : 𝕀) : type =
  comp 0 m os2 [
  | ∂[i] | j=0 → ua os2 os2 (id-equiv/weak-connection os2)
  | j=1 → ua os2 os2 (oloop-equiv i)
  ]

def s2/code/surf : path^1 (path^1 type os2 os2) refl refl =
  s2/code/surf/filler 1

def s2/code (a : s2) : type =
  elim a [
  | base → os2
  | surf i j → s2/code/surf i j
  ]

-- III. encoding function

def s2/encode (a : s2) (p : path s2 base a) : s2/code a =
  coe 0 1 obase in λ k → s2/code (p k)

-- IV. decoding function

def extend-by-surf (p : path s2 base base) (i j k : 𝕀) : s2 =
  comp 0 j (p k) [
  | ∂[i] | k=0 → refl
  | k=1 j → surf i j
  ]

def s2/decode/base (o : os2) : path s2 base base =
  elim o [
  | obase → refl
  | oloop (o' → s2/decode/base/o') i → extend-by-surf s2/decode/base/o' i 1
  ]

def s2/decode (a : s2) : (s2/code a) → path s2 base a =
  elim a [
  | base → s2/decode/base
  | surf i j → λ code k →
    comp 0 1 (extend-by-surf (s2/decode/base (code .cap)) i j k) [
    | ∂[i k] | j=0 → refl
    | j=1 m → s2/decode/base (oloop-onegloop code i m) k
    ]
  ]

-- V. encode base after decode base

def s2/code/proj :
  [i j] (s2/code/surf i j → os2) [
  | (∂[i] | j=1) o → o
  | j=0 o → oloop o i
  ]
  =
  λ i j o →
  comp 0 1 (oloop (o .cap) i) [
  | (∂[i] | j=0) → refl
  | j=1 → oloop-onegloop o i
  ]

def s2/encode-decode/base/step (o : os2) :
  [i j] os2 [
  | ∂[i] → s2/encode base (s2/decode/base o)
  | j=0 → oloop (s2/encode base (s2/decode/base o)) i
  | j=1 → s2/encode base (s2/decode/base (oloop o i))
  ]
  =
  λ i j →
  s2/code/proj i j
    (coe 0 1 obase in λ k →
      s2/code (extend-by-surf (s2/decode/base o) i j k))

def s2/encode-decode/base : (o : os2) → path os2 (s2/encode base (s2/decode base o)) o =
  elim [
  | obase → refl
  | oloop (o' → s2/encode-decode/base/o') i → λ m →
    comp 0 1 (oloop (s2/encode-decode/base/o' m) i) [
    | ∂[i] | m=1 → refl
    | m=0 j → s2/encode-decode/base/step o' i j
    ]
  ]

-- VI. decode base after encode base

def s2/decode-encode/base
  (l : path s2 base base)
  : path (path s2 base base) (s2/decode base (s2/encode base l)) l
  =
  J s2 l (λ p → path (path s2 base (p 1)) (s2/decode (p 1) (s2/encode (p 1) p)) p) refl


-- VII. characterization of the loop space

def Ω1s2/equiv : equiv (path s2 base base) os2 =
  iso→equiv _ _ (s2/encode base, s2/decode base, s2/encode-decode/base, s2/decode-encode/base)
