import path

let pred (x : nat) : nat =
  nat-rec x with
  | zero ⇒ zero
  | suc n ⇒ n
  end

let pred/succ (x : nat) : Path nat x (pred (suc x)) =
  nat-rec x with
  | zero ⇒ λ i → zero
  | suc n ⇒ λ _ → suc n
  end

let plus : nat -> nat -> nat =
  lam m n ->
    nat-rec m with
    | zero => n
    | suc (m => plus/m/n) => suc plus/m/n
    end

let plus/unit/l (n : nat) : Path nat (plus zero n) n =
  lam i -> n

let plus/unit/r (n : nat) : Path nat (plus n zero) n =
  nat-rec n with
  | zero => lam i -> zero
  | suc (n => path/n) => lam i -> suc (path/n i)
  end

let plus/assoc (n : nat) : (m : nat) -> (o : nat) -> Path nat (plus n (plus m o)) (plus (plus n m) o) =
  nat-rec n with
  | zero => lam m o i -> plus m o
  | suc (n => plus/assoc/n) => lam m o i -> suc (plus/assoc/n m o i)
  end

let plus/suc/r (n : nat) : (m : nat) -> Path nat (plus n (suc m)) (suc (plus n m)) =
  nat-rec n with
  | zero => lam m i -> suc m
  | suc (n => plus/n/suc/r) => lam m i -> suc (plus/n/suc/r m i)
  end

let plus/comm (m : nat) : (n : nat) -> Path nat (plus n m) (plus m n) =
  nat-rec m with
  | zero => plus/unit/r
  | suc (m => plus/comm/m) => lam n -> trans _ (suc (plus m n)) (plus/suc/r n m) (lam i -> suc (plus/comm/m n i))
  end
