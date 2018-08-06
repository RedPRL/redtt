import path
import natural
import equivalence
import isotoequiv

data integer where
| ipos of (n : natural)
| inegsu of (n : natural)

let pred (x : integer) : integer =
  elim x with
  | ipos n ⇒
    elim n with
    | ze ⇒ inegsu ze
    | su n ⇒ ipos n
    end
  | inegsu n ⇒ inegsu (su n)
  end

let isu (x : integer) : integer =
  elim x with
  | ipos n ⇒ ipos (su n)
  | inegsu n ⇒
    elim n with
    | ze ⇒ ipos ze
    | su n ⇒ inegsu n
    end
  end


let pred-isu (n : integer) : Path integer (pred (isu n)) n =
  elim n with
  | ipos n => lam _ -> ipos n
  | inegsu n =>
    elim n with
    | ze => lam _ -> inegsu ze
    | su n => lam _ -> inegsu (su n)
    end
  end

let isu-pred (n : integer) : Path integer (isu (pred n)) n =
  elim n with
  | ipos n =>
    elim n with
    | ze => lam _ -> ipos ze
    | su n => lam _ -> ipos (su n)
    end
  | inegsu n => lam _ -> inegsu n
  end

let isu-equiv : Equiv integer integer =
  Iso/Equiv _ _ < isu, < pred, < isu-pred, pred-isu > > >
