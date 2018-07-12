import path

let pred (x : nat) : nat =
  nat-rec x with
  | zero ⇒ zero
  | suc n ⇒ n
  end

let pred/succ/zero (x : nat) : Path nat x (pred (suc x)) =
  nat-rec x with
  | zero ⇒ λ i → zero
  | suc n ⇒ λ _ → suc n
  end
