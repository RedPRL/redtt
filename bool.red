import path

data boolean where
| true
| false

let not (x : boolean) : boolean =
  elim x with
  | true ⇒ false
  | false ⇒ true
  end

let not∘not (x : boolean) : _ =
  not (not x)

let not∘not/id/pt (x : boolean) : Path _ (not∘not x) x =
  elim x with
  | true ⇒ λ _ → true
  | false ⇒ λ _ → false
  end

debug
