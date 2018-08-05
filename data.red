import path

data tree where
| nil
| fork of (lbl : nat) (foo : Path nat lbl lbl) × tree × tree

let test (t : tree) : tree =
  fork zero (λ i → zero) nil nil

