import path

data natural where
| ze
| su of natural

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

debug

; Once the eliminators are being elaborated,
; we can do something like this:

let nat-pred (x : nat) : nat =
  elim x with
  | ze ⇒ zero
  | su n ⇒ n
  end
