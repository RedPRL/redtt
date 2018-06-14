let Path
  (A : type)
  (M : A)
  (N : A)
  : type
  =
  `(# <i> A [i=0 M] [i=1 N])

let funext
  (A : type)
  (B : A → type)
  (f : (x : A) → B x)
  (g : (x : A) → B x)
  (p : (x : A) → Path (B x) (f x) (g x))
  : Path ((x : A) -> B x) f g
  =
  λ i x →
    p x i

let symm
  (A : type)
  (p : `(# <i> A))
  : Path A _ _
  =
  λ i →
   `(hcom 0 1 A (@ p 0)
     [i=0 <j> (@ p j)]
     [i=1 <_> (@ p 0)])

let trans
  (A : type)
  (x : A)
  (p : `(# <i> A))
  (q : Path A (p 1) x)
  : Path A (p 0) (q 1)
  =
  λ i →
   `(hcom 0 1 A (@ p i)
     [i=0 <_> (@ p 0)]
     [i=1 <j> (@ q j)])
