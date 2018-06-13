import path

let J
  (A : type) (a : A)
  (C : (x : A) (p : Path A a x) → type) (d : C a (λ _ → a))
  (x : A) (p : Path A a x)
  : C x p
  =>
  let h : `(# <_ _> A) => λ i j → `(hcom 0 j A a [i=0 <_> a] [i=1 <k> (@ p k)]) in
  let ty : `(# <_> (U 0)) => λ i → C (h i 1) (λ j → h i j) in
  `(coe 0 1 <i> (@ ty i) d)

