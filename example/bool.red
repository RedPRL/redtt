import path

data bool where
| tt
| ff

let not (x : bool) : bool =
  elim x [
  | tt ⇒ ff
  | ff ⇒ tt
  ]

let not∘not (x : bool) : _ =
  not (not x)

let not∘not/id/pt (x : bool) : Path _ (not∘not x) x =
  elim x [
  | tt ⇒ refl
  | ff ⇒ refl
  ]

; Dedicated to Bob ;-)
let shannon (A : type) (f : bool → A) : bool → A =
  λ b →
  elim b [
  | tt ⇒ f tt
  | ff ⇒ f ff
  ]

let shannon/path (A : type) (f : bool → A) : Path _ f (shannon A f) =
  funext _ _ f (shannon A f)
    (λ b →
      elim b [
      | tt ⇒ refl
      | ff ⇒ refl
      ])
