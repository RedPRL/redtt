
let Path [A : type] [M : A] [N : A] : type
Path A M N => `(# <i> A [i=0 M] [i=1 N])

let funext
  [A : type]
  [B : `(→ A (U 0))]
  [f : `(→ [x : A] (B x))]
  [g : `(→ [x : A] (B x))]
  [p : `(→ [x : A] (call (Path (B x) (f x) (g x))))]
  : `(call (Path (→ [x : A] (B x)) f g))

funext A B f g p =>
  ?
  ; `(λ <i> [x] (@ (p x) i))


