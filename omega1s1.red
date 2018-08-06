import path
import integer

let UA (A,B : type) (E : Equiv A B) : Path^1 type A B =
  λ i →
    `(V i A B E)


let S1-univ-cover (x : S1) : type =
  S1-rec x with
  | base => integer
  | loop i => UA _ _ isu-equiv i
  end

let loopn (n : integer) : Path S1 base base =
  elim n with
  | ipos n =>
    elim n with
    | ze => lam _ -> base
    | su (n => loopn) => trans S1 (lam i -> loop i) loopn
    end
  | inegsu n =>
    elim n with
    | ze => symm S1 (lam i -> loop i)
    | su (n => loopn) => trans S1 (symm S1 (lam i -> loop i)) loopn
    end
  end

let winding (l : Path S1 base base) : integer =
  coe 0 1 (ipos ze) in lam i -> S1-univ-cover (l i)

let two : integer = ipos (su (su ze))

let winding-loop-testing0 : Path integer two (winding (loopn two)) =
  lam _ -> two

let five : integer = ipos (su (su (su (su ze))))

let winding-loop-testing1 : Path integer five (winding (loopn five)) =
  lam _ -> five
