import path
import integer

let S1-univ-cover (x : S1) : type =
  S1-rec x with
  | base => int
  | loop i => `(V i int int succ-equiv)
  end

let loopn (n : int) : Path S1 base base =
  int-rec n with
  | pos n =>
    nat-rec n with
    | zero => lam _ -> base
    | suc (n => loopn) => trans S1 (lam i -> loop i) loopn
    end
  | negsuc n =>
    nat-rec n with
    | zero => symm S1 (lam i -> loop i)
    | suc (n => loopn) => trans S1 (symm S1 (lam i -> loop i)) loopn
    end
  end

let winding (l : Path S1 base base) : int =
  coe 0 1 (pos zero) in lam i -> S1-univ-cover (l i)

let two : int = pos (suc (suc zero))

let winding-loop-testing : Path int two (winding (trans S1 (lam i -> loop i) (lam i -> loop i))) =
  lam _ -> two

; TODO: a bug prevents the following from working

let winding-loop-testing : Path int two (winding (loopn two)) =
  lam _ -> two
