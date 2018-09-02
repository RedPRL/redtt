import path
import bool

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
  coe 0 1 xs.1 in λ i →
    later (dfix[i] A : type in stream/F A)

let tts : _ =
  fix xs : stream in
    stream/cons tt xs
