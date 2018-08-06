data foo where
| p
| q (x : foo) <i>

let asdf : foo =
  q p 0

let test (x : foo) : foo =
  elim x with
  | p ⇒ p
  | q (z ⇒ ih) j ⇒ q ih j
  end
