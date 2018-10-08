import path
import bool

-- the core constructor (prev α M) is written using application notation in
-- the surface language
def stream/F (A : ✓ → type) : type =
  bool × (α : ✓) → A α

def stream/L (i : dim) : type =
  fix[i] A : type in stream/F A

def stream : _ = stream/L 0

def later (A : ✓ → type) : type =
  (α : ✓) → A α

def stream/cons (x : bool) (xs : ✓ → stream) : stream =
  ( x,
    coe 1 0 xs in λ i →
      later (dfix[i] A : type in stream/F A)
  )

def stream/hd (xs : stream) : _ =
  xs.fst

def stream/tl (xs : stream) : ✓ → stream =
  coe 0 1 (xs.snd) in λ i →
    later (dfix[i] A : type in stream/F A)

def tts : stream =
  fix xs : stream in
    stream/cons tt xs
