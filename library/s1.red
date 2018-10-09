import path
import connection
import equivalence
import univalence

data s1 where
| base
| loop (i : 𝕀) [∂[i] → base]

def rotate/loop : (a : s1) → path _ a a =
  elim [
  | base → λ j → loop j
  | loop i → λ j → connection/both s1 (λ k → loop k) (λ k → loop k) i j
  ]

def rotate : s1 → s1 → s1 =
  elim [
  | base → λ b → b
  | loop i → λ b → rotate/loop b i
  ]

def rotate/equiv/loop : path _ (id-equiv s1) (id-equiv s1) =
  λ i →
    let fwd (j : 𝕀) (a : s1) = rotate/loop a j in
    ( fwd i
    , prop→prop-over
      (λ j → is-equiv s1 s1 (fwd j))
      (is-equiv/prop/direct s1 s1 (λ a → a))
      (id-equiv s1 .snd)
      (id-equiv s1 .snd)
      i
    )

def rotate/is-equiv : (a : s1) → is-equiv s1 s1 (rotate a) =
  elim [
  | base → id-equiv s1 .snd
  | loop i → rotate/equiv/loop i .snd
  ]

def rotate/equiv (a : s1) : equiv s1 s1 =
  (rotate a , rotate/is-equiv a)

def rotate/path (a : s1) : path^1 type s1 s1 =
  ua s1 s1 (rotate/equiv a)
