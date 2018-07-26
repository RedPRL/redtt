import path

let nat-pred (x : nat) : nat =
  nat-rec x with
  | zero ⇒ zero
  | suc n ⇒ n
  end

let nat-pred/succ (x : nat) : Path nat x (nat-pred (suc x)) =
  nat-rec x with
  | zero ⇒ λ i → zero
  | suc n ⇒ λ _ → suc n
  end

let plus : nat → nat → nat =
  λ m n →
    nat-rec m with
    | zero ⇒ n
    | suc (m ⇒ plus/m/n) ⇒ suc plus/m/n
    end

let plus/unit/l (n : nat) : Path nat (plus zero n) n =
  λ i → n

let plus/unit/r (n : nat) : Path nat (plus n zero) n =
  nat-rec n with
  | zero ⇒ λ i → zero
  | suc (n ⇒ path/n) ⇒ λ i → suc (path/n i)
  end

let plus/assoc (n : nat) : (m, o : nat) → Path nat (plus n (plus m o)) (plus (plus n m) o) =
  nat-rec n with
  | zero ⇒ λ m o i → plus m o
  | suc (n ⇒ plus/assoc/n) ⇒ λ m o i → suc (plus/assoc/n m o i)
  end

let plus/suc/r (n : nat) : (m : nat) → Path nat (plus n (suc m)) (suc (plus n m)) =
  nat-rec n with
  | zero ⇒ λ m i → suc m
  | suc (n ⇒ plus/n/suc/r) ⇒ λ m i → suc (plus/n/suc/r m i)
  end

let plus/comm (m : nat) : (n : nat) → Path nat (plus n m) (plus m n) =
  nat-rec m with
  | zero ⇒ plus/unit/r
  | suc (m ⇒ plus/comm/m) ⇒ λ n → trans _ (suc (plus m n)) (plus/suc/r n m) (λ i → suc (plus/comm/m n i))
  end

