import path

let Ltr (A : type) : type =
  `(▷ [_] A)

let Fix (F : (Ltr^1 type) → type) : Line^1 type =
  λ i →
    F `(dfix i (U 0) [A] (F A))

let stream/F (A : `(▷ [_] (U 0))) : type =
  bool × `(▷ [α] (prev α A))

let stream/L : Line^1 type =
  Fix stream/F

let stream : type = stream/L 0

let stream/cons (x : bool) (xs : Ltr stream) : stream =
  < x,
    coe 1 0 xs in λ i →
      `(▷ [α]
        (prev α
         (dfix i (U 0) [A] (stream/F A))))
  >

let stream/hd (xs : stream) : bool =
  xs.0

let stream/tl (xs : stream) : Ltr stream =
  coe 0 1 (xs.1) in λ i →
    `(▷ [α]
      (prev α
       (dfix i (U 0) [A] (stream/F A))))


debug
