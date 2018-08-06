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


data natural where
| ze
| su of natural

let nat-pred (x : natural) : natural =
  elim x with
  | ze ⇒ ze
  | su n ⇒ n
  end


let nat-pred/su (x : natural) : Path natural x (nat-pred (su x)) =
  λ _ → x

let plus : natural → natural → natural =
  λ m n →
    elim m with
    | ze ⇒ n
    | su (m ⇒ plus/m/n) ⇒ su plus/m/n
    end

let plus/unit/l (n : natural) : Path natural (plus ze n) n =
  λ i → n

let plus/unit/r (n : natural) : Path natural (plus n ze) n =
  elim n with
  | ze ⇒ λ _ → ze
  | su (n ⇒ path/n) ⇒ λ i → su (path/n i)
  end

let plus/assoc (n : natural) : (m, o : natural) → Path natural (plus n (plus m o)) (plus (plus n m) o) =
  elim n with
  | ze ⇒ λ m o i → plus m o
  | su (n ⇒ plus/assoc/n) ⇒ λ m o i → su (plus/assoc/n m o i)
  end

let plus/su/r (n : natural) : (m : natural) → Path natural (plus n (su m)) (su (plus n m)) =
  elim n with
  | ze ⇒ λ m _ → su m
  | su (n ⇒ plus/n/su/r) ⇒ λ m i → su (plus/n/su/r m i)
  end


let plus/comm (m : natural) : (n : natural) → Path natural (plus n m) (plus m n) =
  elim m with
  | ze ⇒ plus/unit/r
  | su (m ⇒ plus/comm/m) ⇒ λ n → trans _ (plus/su/r n m) (λ i → su (plus/comm/m n i))
  end

