import path

; to be able to program with this, I really need the dimension-indexed dfix.

let fix (F : `(▷ [_] (U 0)) → type) : Line^1 type =
  λ i →
    F `(dfix i (U 0) [A] (F A))

let stream/F (A : `(▷ [_] (U 0))) : type =
  bool × `(▷ [α] (prev α A))

let stream : Line^1 type =
  fix stream/F

 let stream/cons (x : bool) (xs : `(▷ [_] (@ stream 0))) : stream 0 =
   < x,
     coe 1 0 xs in λ i →
       `(▷ [α] (prev α (dfix i (U 0) [A] (stream/F A))))
   >

debug
