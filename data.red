data tree where
| nil
| fork of (lbl : nat) × tree × tree

let test (t : tree) : tree =
  fork zero nil nil

debug

