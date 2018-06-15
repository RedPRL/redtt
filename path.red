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
  : Path A (p 1) (p 0)
  =
  λ i →
    comp 0 1 (p 0) with
    | i=0 ⇒ p
    | i=1 ⇒ λ _ → p 0
    end

let trans
  (A : type)
  (x : A)
  (p : `(# <i> A))
  (q : Path A (p 1) x)
  : Path A (p 0) (q 1)
  =
  λ i →
    comp 0 1 (p i) with
    | i=0 ⇒ λ _ → p 0
    | i=1 ⇒ q
    end
