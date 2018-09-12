import path
import J
import equivalence
import isotoequiv
import univalence
import s2

-- a calculation of the loop space of the 2-sphere, based on
-- https://egbertrijke.com/2016/09/28/the-loop-space-of-the-2-sphere/

-- loop space of s2
data os2 where
| obase
| oloop (y : os2) @ i [∂[i] → y]

-- I. the loop of automorphisms of os2

-- for the definition of s2/decode, it is convenient to use an id-equiv where
-- both inverses are reflexivities
let id-equiv/wc : (B : type) → equiv B B = id-equiv/weak-connection

-- it would probably be more efficient to define this directly,
-- but we don't need it
let oloop-equiv : path (equiv os2 os2) (id-equiv/wc os2) (id-equiv/wc os2) =
  λ i →
    ( λ o → oloop o i
    , prop→prop-over
      (λ j → is-equiv os2 os2 (λ o → oloop o j))
      (is-equiv/prop/direct os2 os2 (λ o → o))
      (id-equiv/wc os2 .snd)
      (id-equiv/wc os2 .snd)
      i
    )

-- incidentally, onegloop o is homotopic to symm (λ i → oloop o i)
let onegloop (o : os2) : path os2 o o =
  λ i → oloop-equiv i .snd o .fst .fst

let oloop-onegloop (o : os2)
  : pathd (λ i → path os2 (oloop (onegloop o i) i) o) refl refl
  =
  λ i → oloop-equiv i .snd o .fst .snd

let onegloop-oloop (o : os2)
  : pathd (λ i → path os2 (onegloop (oloop o i) i) o) refl refl
  =
  λ i j →
    comp 0 1 o [
    | ∂[i] | j=1 → refl
    | j=0 k → oloop-equiv i .snd (oloop o i) .snd (o, refl) k .fst
    ]

-- II. universal cover over s2

let s2/code/surf/filler (m i j : dim) : type =
  comp 0 m os2 [
  | ∂[i] | j=0 → ua os2 os2 (id-equiv/wc os2)
  | j=1 → ua os2 os2 (oloop-equiv i)
  ]

let s2/code/surf : path^1 (path^1 type os2 os2) refl refl =
  s2/code/surf/filler 1

let s2/code/proj :
  [i j] (s2/code/surf i j → os2) [
  | (∂[i] | j=1) o → o
  | j=0 o → oloop o i
  ]
  =
  λ i j →
  comp 0 1 (λ o → oloop o i) in (λ m → s2/code/surf/filler m i j → os2) [
  | ∂[i] → ua/proj os2 os2 (id-equiv/wc os2)
  | j=0 m o → oloop (ua/proj os2 os2 (id-equiv/wc os2) m o) i
  | j=1 → ua/proj os2 os2 (oloop-equiv i)
  ]

let s2/code (a : s2) : type =
  elim a [
  | base → os2
  | surf i j → s2/code/surf i j
  ]

-- III. encoding function

let s2/encode (a : s2) (p : path s2 base a) : s2/code a =
  coe 0 1 obase in λ k → s2/code (p k)

-- IV. decoding function

let extend-by-surf (p : path s2 base base) (i j k : dim) : s2 =
  comp 0 j (p k) [
  | ∂[i] | k=0 → refl
  | k=1 j → surf i j
  ]

let s2/decode/base (o : os2) : path s2 base base =
  elim o [
  | obase → refl
  | oloop (o' → s2/decode/base/o') i → extend-by-surf s2/decode/base/o' i 1
  ]

let s2/decode (a : s2) : (s2/code a) → path s2 base a =
  elim a [
  | base → s2/decode/base
  | surf i j → λ code k →
    comp 0 1 (extend-by-surf (s2/decode/base (onegloop (s2/code/proj i j code) i)) i j k) [
    | ∂[i k] → refl
    | j=0 m → s2/decode/base (onegloop-oloop code i m) k
    | j=1 m → s2/decode/base (oloop-onegloop code i m) k
    ]
  ]

-- V. encode base after decode base

let s2/encode-decode/base/step (o : os2) :
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

let s2/encode-decode/base (o : os2)
  : path os2 (s2/encode base (s2/decode base o)) o
  =
  elim o [
  | obase → refl
  | oloop (o' → s2/encode-decode/base/o') i → λ m →
    comp 0 1 (oloop (s2/encode-decode/base/o' m) i) [
    | ∂[i] | m=1 → refl
    | m=0 j → s2/encode-decode/base/step o' i j
    ]
  ]

-- VI. decode base after encode base

let s2/decode-encode/base (l : path s2 base base)
  : path (path s2 base base) (s2/decode base (s2/encode base l)) l
  =
  J s2 base (λ a p → path (path s2 base a) (s2/decode a (s2/encode a p)) p) refl base l

-- VII. characterization of the loop space

let s2/loop-space-equiv : equiv (path s2 base base) os2 =
  iso→equiv _ _ (s2/encode base, s2/decode base, s2/encode-decode/base, s2/decode-encode/base)
