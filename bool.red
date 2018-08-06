import path

data bool where
| tt
| ff

let not (x : bool) : bool =
  elim x with
  | tt ⇒ ff
  | ff ⇒ tt
  end

let not∘not (x : bool) : _ =
  not (not x)

let not∘not/id/pt (x : bool) : Path _ (not∘not x) x =
  elim x with
  | tt ⇒ λ _ → tt
  | ff ⇒ λ _ → ff
  end
