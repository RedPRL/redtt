import path
import natural
import equivalence

let pred (x : int) : int =
  int-rec x with
  | pos n ⇒
    nat-rec n with
    | zero ⇒ negsuc zero
    | suc n ⇒ pos n
    end
  | negsuc n ⇒ negsuc (suc n)
  end

let succ (x : int) : int =
  int-rec x with
  | pos n ⇒ pos (suc n)
  | negsuc n ⇒
    nat-rec n with
    | zero ⇒ pos zero
    | suc n ⇒ negsuc n
    end
  end

let pred-succ (n : int) : Path int (pred (succ n)) n =
  int-rec n with
  | pos n => lam _ -> pos n
  | negsuc n =>
    nat-rec n with
    | zero => lam _ -> negsuc zero
    | suc n => lam _ -> negsuc (suc n)
    end
  end

let succ-pred (n : int) : Path int (succ (pred n)) n =
  int-rec n with
  | pos n =>
    nat-rec n with
    | zero => lam _ -> pos zero
    | suc n => lam _ -> pos (suc n)
    end
  | negsuc n => lam _ -> negsuc n
  end
