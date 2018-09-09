import path
import connection
import equivalence
import univalence

data s1 where
| base
| loop @ i [∂[i] → base]

let rotate/loop (a : s1) : Path _ a a =
  elim a [
  | base → λ j → loop j
  | loop i → λ j → connection/both s1 (λ k → loop k) (λ k → loop k) i j
  ]

let rotate (a : s1) : s1 → s1 =
  elim a [
  | base → λ b → b
  | loop i → λ b → rotate/loop b i
  ]

let rotate/equiv/loop : Path _ (IdEquiv s1) (IdEquiv s1) =
  λ i →
    let fwd : dim → s1 → s1 =
      λ j a → rotate/loop a j
    in
    ( fwd i
    , PropToPropOver
      (λ j → IsEquiv s1 s1 (fwd j))
      (PropIsEquivDirect s1 s1 (λ a → a))
      (IdEquiv s1 .snd)
      (IdEquiv s1 .snd)
      i
    )

let rotate/is-equiv (a : s1) : IsEquiv s1 s1 (rotate a) =
  elim a [
  | base → IdEquiv s1 .snd
  | loop i → rotate/equiv/loop i .snd
  ]

let rotate/equiv (a : s1) : Equiv s1 s1 =
  ( rotate a , rotate/is-equiv a )

let rotate/path (a : s1) : Path^1 type s1 s1 =
  UA s1 s1 (rotate/equiv a)
