import path

let pred (x : nat) : nat =
  nat-rec x with
  | zero ⇒ zero
  | suc (n ⇒ ih) ⇒ n
  end

; broken
let nat/refl (x : nat) : Path nat x x =
  nat-rec x with
  | zero ⇒ λ _ → zero
  | suc n ⇒ λ _ → suc n
  end

