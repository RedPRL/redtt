import path

let Fix (A : type) (f : (✓ → A) → A) : Line A =
  λ i →
    f `(dfix i A [x] (f x))

; the core constructor (prev α M) is written using application notation in
; the surface language
let stream/F (A : ✓ → type) : type =
  bool × (α : ✓) → A α

let stream/L : Line^1 type =
  Fix^1 _ stream/F

let stream : type = stream/L 0

let stream/cons (x : bool) (xs : ✓ → stream) : stream =
  < x,
    coe 1 0 xs in λ i →
      (α : ✓) →
        `(dfix i (U 0) [A] (stream/F A)) α
  >


let stream/hd (xs : stream) : bool =
  xs.0

let stream/tl (xs : stream) (α : ✓) : stream =
  coe 0 1 (xs.1 α) in λ i →
    `(dfix i (U 0) [A] (stream/F A)) α

let tts : stream =
  Fix _ (stream/cons tt) 0

; To eliminate a box, write 'b !'; this elaborates to the core term `(open b).
let bool/constant (x : bool) : (b : □ bool) × Path bool x (b !) =
  if x then
    < shut tt, λ _ → tt >
  else
    < shut ff, λ _ → ff >

let sequence : type = □ stream

let sequence/cons (x : bool) (xs : sequence) : sequence =
  shut
    stream/cons
      (bool/constant x .0 !)
      (λ _ → xs !)

let sequence/hd (xs : sequence) : bool =
  stream/hd (xs !)

let sequence/tl (xs : sequence) : sequence =
  shut
    stream/tl (xs !) ∙

debug
