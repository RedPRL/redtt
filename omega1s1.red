import path
import integer
import univalence

let S1-univ-cover (x : S1) : type =
  S1-rec x with
  | base => int
  | loop i => UA int int succ-equiv i
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

let three : int = pos (suc (suc (suc zero)))

let winding-loop-testing : Path int three (winding (loopn three)) =
  lam _ -> three
