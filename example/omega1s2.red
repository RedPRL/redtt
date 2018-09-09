import path
import J
import equivalence
import isotoequiv
import univalence
import s2

; a calculation of the loop space of the 2-sphere, based on
; https://egbertrijke.com/2016/09/28/the-loop-space-of-the-2-sphere/

; loop space of s2
data os2 where
| obase
| oloop (y : os2) @ i [∂[i] → y]

; I. the loop of automorphisms of os2

; for the definition of s2/decode, it is convenient to use an IdEquiv where
; both inverses are reflexivities
let IdEquiv/wc : (B : type) → Equiv B B = IdEquiv/weak-connection

; it would probably be more efficient to define this directly,
; but we don't need it
let oloop-equiv : Path (Equiv os2 os2) (IdEquiv/wc os2) (IdEquiv/wc os2) =
  λ i →
    ( λ o → oloop o i
    , PropToPropOver
      (λ j → IsEquiv os2 os2 (λ o → oloop o j))
      (PropIsEquivDirect os2 os2 (λ o → o))
      (IdEquiv/wc os2 .snd)
      (IdEquiv/wc os2 .snd)
      i
    )

; incidentally, onegloop o is homotopic to symm (λ i → oloop o i)
let onegloop (o : os2) : Path os2 o o =
  λ i → oloop-equiv i .snd o .fst .fst

let oloop-onegloop (o : os2)
  : PathD (λ i → Path os2 (oloop (onegloop o i) i) o) refl refl
  =
  λ i → oloop-equiv i .snd o .fst .snd

let onegloop-oloop (o : os2)
  : PathD (λ i → Path os2 (onegloop (oloop o i) i) o) refl refl
  =
  λ i j →
    comp 0 1 o [
    | ∂[i] | j=1 → refl
    | j=0 k → oloop-equiv i .snd (oloop o i) .snd (o, refl) k .fst
    ]

; II. universal cover over s2

let s2/Code/Surf/filler (m i j : dim) : type =
  comp 0 m os2 [
  | ∂[i] | j=0 → UA os2 os2 (IdEquiv/wc os2)
  | j=1 → UA os2 os2 (oloop-equiv i)
  ]

let s2/Code/Surf : Path^1 (Path^1 type os2 os2) refl refl =
  s2/Code/Surf/filler 1

let s2/Code/proj :
  [i j] (s2/Code/Surf i j → os2) [
  | (∂[i] | j=1) o → o
  | j=0 o → oloop o i
  ]
  =
  λ i j →
  comp 0 1 (λ o → oloop o i) in (λ m → s2/Code/Surf/filler m i j → os2) [
  | ∂[i] → UAproj os2 os2 (IdEquiv/wc os2)
  | j=0 m o → oloop (UAproj os2 os2 (IdEquiv/wc os2) m o) i
  | j=1 → UAproj os2 os2 (oloop-equiv i)
  ]

let s2/Code (a : s2) : type =
  elim a [
  | base → os2
  | surf i j → s2/Code/Surf i j
  ]

; III. encoding function

let s2/encode (a : s2) (p : Path s2 base a) : s2/Code a =
  coe 0 1 obase in λ k → s2/Code (p k)

; IV. decoding function

let extend-by-surf (p : Path s2 base base) (i j k : dim) : s2 =
  comp 0 j (p k) [
  | ∂[i] | k=0 → refl
  | k=1 j → surf i j
  ]

let s2/decode/base (o : os2) : Path s2 base base =
  elim o [
  | obase → refl
  | oloop (o' → s2/decode/base/o') i → extend-by-surf s2/decode/base/o' i 1
  ]

let s2/decode (a : s2) : (s2/Code a) → Path s2 base a =
  elim a [
  | base → s2/decode/base
  | surf i j → λ code k →
    comp 0 1 (extend-by-surf (s2/decode/base (onegloop (s2/Code/proj i j code) i)) i j k) [
    | ∂[i k] → refl
    | j=0 m → s2/decode/base (onegloop-oloop code i m) k
    | j=1 m → s2/decode/base (oloop-onegloop code i m) k
    ]
  ]

; V. encode base after decode base

let s2/encode-decode/base/step (o : os2) :
  [i j] os2 [
  | ∂[i] → s2/encode base (s2/decode/base o)
  | j=0 → oloop (s2/encode base (s2/decode/base o)) i
  | j=1 → s2/encode base (s2/decode/base (oloop o i))
  ]
  =
  λ i j →
    s2/Code/proj i j
      (coe 0 1 obase in λ k →
        s2/Code (extend-by-surf (s2/decode/base o) i j k))

let s2/encode-decode/base (o : os2)
  : Path os2 (s2/encode base (s2/decode base o)) o
  =
  elim o [
  | obase → refl
  | oloop (o' → s2/encode-decode/base/o') i → λ m →
    comp 0 1 (oloop (s2/encode-decode/base/o' m) i) [
    | ∂[i] | m=1 → refl
    | m=0 j → s2/encode-decode/base/step o' i j
    ]
  ]

; VI. decode base after encode base

let s2/decode-encode/base (l : Path s2 base base)
  : Path (Path s2 base base) (s2/decode base (s2/encode base l)) l
  =
  J s2 base (λ a p → Path (Path s2 base a) (s2/decode a (s2/encode a p)) p) refl base l

; VII. characterization of the loop space

let s2/loop-space-equiv : Equiv (Path s2 base base) os2 =
  Iso/Equiv _ _ (s2/encode base, s2/decode base, s2/encode-decode/base, s2/decode-encode/base)
