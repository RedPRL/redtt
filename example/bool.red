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
  | tt ⇒ auto
  | ff ⇒ auto
  ]
