import list

-- In this file, we try to relate the weak free monoid on a set (presented as a HIT) to the
-- strict free monoid, presented as a list.

-- Probably need to truncate this to get the right type
data F (A : type) where
| η (a : A)
| ☆ (s t : F)
| ε
| idn/r (s : F) (i : dim) [
  | i=0 → ☆ s ε
  | i=1 → s
  ]
| idn/l (s : F) (i : dim) [
  | i=0 → ☆ ε s
  | i=1 → s
  ]
| ass (s t u : F) (i : dim) [
  | i=0 → ☆ s (☆ t u)
  | i=1 → ☆ (☆ s t) u
  ]


let quote (A : type) : list A → F A =
  elim [
  | nil → ε
  | cons x (xs → ih) →
    ☆ (η x) ih
  ]


let eval (A : type) : F A → list A =
  elim [
  | η a →
    cons a nil
  | ☆ (s → ih/s) (t → ih/t) →
    append A ih/s ih/t
  | ε →
    nil
  | idn/l s i →
    refl
  | idn/r (s → ih/s) i →
    append/idn/r A ih/s i
  | ass (s → ih/s) (t → ih/t) (u → ih/u) i →
    append/ass A ih/s ih/t ih/u i
  ]

let nbe (A : type) (s : F A) : F A =
  quote A (eval A s)


/-
-- need to do some kind of gluing thing I guess
let soundness (A : type) : (s : F A) → path _ s (nbe A s) =
  elim [

  | ☆ (s → ih/s) (t → ih/t) →
    ?

  | idn/l s i →
    ?_
  | idn/r (s → ih/s) i →
    ?_
  | ass (s → ih/s) (t → ih/t) (u → ih/u) i →
    ?_

  | * → refl
  ]
-/
