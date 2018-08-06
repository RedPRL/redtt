import path


data nat where
| zero
| suc (x : nat)

let nat-pred (x : nat) : nat =
  elim x with
  | zero ⇒ zero
  | suc n ⇒ n
  end


let nat-pred/suc (x : nat) : Path nat x (nat-pred (suc x)) =
  λ _ → x

let plus : nat → nat → nat =
  λ m n →
    elim m with
    | zero ⇒ n
    | suc (m ⇒ plus/m/n) ⇒ suc plus/m/n
    end

let plus/unit/l (n : nat) : Path nat (plus zero n) n =
  λ i → n

let plus/unit/r (n : nat) : Path nat (plus n zero) n =
  elim n with
  | zero ⇒ λ _ → zero
  | suc (n ⇒ path/n) ⇒ λ i → suc (path/n i)
  end

let plus/assoc (n : nat) : (m, o : nat) → Path nat (plus n (plus m o)) (plus (plus n m) o) =
  elim n with
  | zero ⇒ λ m o i → plus m o
  | suc (n ⇒ plus/assoc/n) ⇒ λ m o i → suc (plus/assoc/n m o i)
  end

let plus/suc/r (n : nat) : (m : nat) → Path nat (plus n (suc m)) (suc (plus n m)) =
  elim n with
  | zero ⇒ λ m _ → suc m
  | suc (n ⇒ plus/n/suc/r) ⇒ λ m i → suc (plus/n/suc/r m i)
  end


let plus/comm (m : nat) : (n : nat) → Path nat (plus n m) (plus m n) =
  elim m with
  | zero ⇒ plus/unit/r
  | suc (m ⇒ plus/comm/m) ⇒ λ n → trans _ (plus/suc/r n m) (λ i → suc (plus/comm/m n i))
  end

