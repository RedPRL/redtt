import path

; the core constructor (prev α M) is written using application notation in
; the surface language
let stream/F (A : ✓ → type) : type =
  bool × (α : ✓) → A α

let stream/L (i : dim) : type =
  fix[i] A : type in stream/F A

let stream : _ = stream/L 0

let later (A : ✓ → type) : type =
  (α : ✓) → A α

let stream/cons (x : bool) (xs : ✓ → stream) : stream =
  < x,
    coe 1 0 xs in λ i →
      later (dfix[i] A : type in stream/F A)
  >

let stream/hd (xs : stream) : _ =
  xs.0

let stream/tl (xs : stream) : ✓ → stream =
  coe 0 1 (xs.1) in λ i →
    later (dfix[i] A : type in stream/F A)

let tts : _ =
  fix xs : stream in
    stream/cons tt xs


; To eliminate a box, write 'b !'; this elaborates to the core term `(open b).
let bool/constant (x : bool) : (b : □ bool) × Path _ x (b !) =
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


let law/k (A,B : type) (f : □ (A → B)) (x : □ A) : □ B =
  shut f ! (x !)
