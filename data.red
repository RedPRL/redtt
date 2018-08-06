import path

data tree where
| nil
| fork of (lbl : nat) (foo : Path _ lbl lbl) × tree × tree

; an example that exercises definitional equivalence for constructors
let test (t : tree)
  : restrict tree with
    | 0=0 ⇒ fork zero (λ _ → zero) t nil
    end
  =
  fork _ (λ _ → zero) t nil

data void where

let abort (A : type) (t : void) : A =
  elim t with end

