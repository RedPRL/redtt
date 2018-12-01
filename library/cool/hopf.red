import prelude
import data.s1
import data.s2
import basics.isotoequiv

def rotate/loop : (a : s1) → path _ a a =
  elim [
  | base → λ j → loop j
  | loop i → λ j → connection/both s1 (λ k → loop k) (λ k → loop k) i j
  ]

def unrotate/loop (a : s1) : path _ a a =
  symm s1 (rotate/loop a)

def rotate-unrotate/loop (a : s1)
  : pathd (λ i → path s1 (rotate/loop (unrotate/loop a i) i) a) refl refl
  =
  λ i j →
  comp 0 1 (rotate/loop a i) [
  | i=0 k → rotate/loop a k
  | i=1 → refl
  | j=0 k → rotate/loop (symm/filler s1 (λ i → rotate/loop a i) k i) i
  | j=1 k → weak-connection/or s1 (λ i → rotate/loop a i) i k
  ]

def unrotate-rotate/loop (a : s1)
  : pathd (λ i → path s1 (unrotate/loop (rotate/loop a i) i) a) refl refl
  =
  λ i j →
  let filler (m : 𝕀) : s1 =
    comp 1 m a [
    | j=0 m → rotate/loop a m
    | j=1 → refl
    ]
  in
  comp 0 1 (filler i) [
  | i=0 → filler
  | i=1 | j=1 → refl
  ]

def rotate/loop/equiv (i : 𝕀) : equiv s1 s1 =
  iso→equiv s1 s1
    ( λ a → rotate/loop a i
    , λ a → unrotate/loop a i
    , λ a → rotate-unrotate/loop a i
    , λ a → unrotate-rotate/loop a i
    )

def hopf : s2 → type =
  elim [
  | base → s1
  | surf i j →
    comp 0 1 s1 [
    | ∂[j] | i=0 → ua s1 s1 (rotate/loop/equiv 0)
    | i=1 → ua s1 s1 (rotate/loop/equiv j)
    ]
  ]
