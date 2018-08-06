import path
import nat
import equivalence
import isotoequiv

data int where
| pos of (n : nat)
| negsuc of (n : nat)

let pred (x : int) : int =
  elim x with
  | pos n ⇒
    elim n with
    | zero ⇒ negsuc zero
    | suc n ⇒ pos n
    end
  | negsuc n ⇒ negsuc (suc n)
  end

let isuc (x : int) : int =
  elim x with
  | pos n ⇒ pos (suc n)
  | negsuc n ⇒
    elim n with
    | zero ⇒ pos zero
    | suc n ⇒ negsuc n
    end
  end


let pred-isuc (n : int) : Path int (pred (isuc n)) n =
  elim n with
  | pos n => lam _ -> pos n
  | negsuc n =>
    elim n with
    | zero => lam _ -> negsuc zero
    | suc n => lam _ -> negsuc (suc n)
    end
  end

let isuc-pred (n : int) : Path int (isuc (pred n)) n =
  elim n with
  | pos n =>
    elim n with
    | zero => lam _ -> pos zero
    | suc n => lam _ -> pos (suc n)
    end
  | negsuc n => lam _ -> negsuc n
  end

let isuc-equiv : Equiv int int =
  Iso/Equiv _ _ < isuc, < pred, < isuc-pred, pred-isuc > > >
