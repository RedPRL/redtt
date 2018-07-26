import path

; Currently, the source language doesn't have constructs for guarded recursion,
; so you must program it using the *redtt core language*. This language is accessed
; using a backtick `expr.

let Ltr (A : type) : type =
  `(▷ [_] A)

let Fix (A : type) (f : (Ltr A) → A) : Line A =
  λ i →
    f `(dfix i A [x] (f x))

let stream/F (A : `(▷ [_] (U 0))) : type =
  bool × `(▷ [α] (prev α A))

let stream/L : Line^1 type =
  Fix^1 _ stream/F

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

let tts : stream =
  Fix stream (stream/cons tt) 0




let box/example (x : bool) : (b : `(□ bool)) × Path bool x `(open b) =
  if x then
    < `(shut tt), λ _ → tt >
  else
    < `(shut ff), λ _ → ff >

debug
