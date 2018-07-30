import path

let Fix (A : type) (f : (✓ → A) → A) : Line A =
  λ i →
    f `(dfix i A [x] (f x))

; the core constructor (prev α M) is written using application notation in
; the surface language
let stream/F (A : ✓ → type) : type =
  bool × (α : ✓) → A α

let stream/L : Line^1 _ =
  Fix^1 _ stream/F

let stream : _ = stream/L 0

let stream/cons (x : bool) (xs : ✓ → stream) : stream =
  < x,
    coe 1 0 xs in λ i →
      (α : ✓) →
        `(dfix i (U 0) [A] (stream/F A)) α
  >


let stream/hd (xs : stream) : _ =
  xs.0

let stream/tl (xs : stream) (α : ✓) : stream =
  coe 0 1 (xs.1 α) in λ i →
    `(dfix i (U 0) [A] (stream/F A)) α

let tts : _ =
  Fix _ (stream/cons tt) 0

; To eliminate a box, write 'b !'; this elaborates to the core term `(open b).
let bool/constant (x : bool) : (b : □ bool) × Path _ x (b !) =
  if x then
    < shut tt, λ _ → tt >
  else
    < shut ff, λ _ → ff >

let sequence : type = □ stream


let Next (A : type) (x : A) ✓ : A =
  x

let sequence/cons (x : bool) (xs : sequence) : sequence =
  shut
    stream/cons
      (bool/constant x .0 !)
      (Next stream (xs !))
      ; this is suspicious: we use this Next in order to essentially
      ; weaken away the tick that we will not use, in order to get the right number
      ; of locks deleted. But this is proof-theoretically very strange.

; The proper solution to the problem above is to bind lock names in the syntax and in the context,
; analogous to tick names. This will make the calculus more baroque, but it will enable a
; deterministic version of the 'open' rule. The source term for the above would then be:
;
;     λ α → stream/cons (bool/constant x .0 α) (λ β → xs α)
;
; Above, α is a lock name and β is a tick name; opening with the lock α
; would *delete* the tick β from the context (thinking backward), which is
; a tick weakening. the example would typecheck because there is no need for
; β in xs.



let sequence/hd (xs : sequence) : bool =
  stream/hd (xs !)

let sequence/tl (xs : sequence) : sequence =
  shut
    stream/tl (xs !) ∙


let law/k (A,B : type) (f : □ (A → B)) (x : □ A) : □ B =
  shut f ! (x !)
