import path

let J
  (A : type) (a : A)
  (C : (x : A) (p : Path _ a x) → type) (d : C a (λ _ → a))
  (x : A) (p : Path _ a x)
  : C x p
  =
  let h : `(# <_ _> A) = λ i j → `(hcom 0 j A a [i=0 <_> a] [i=1 <k> (@ p k)]) in
  let ty : `(# <_> (U 0)) = λ i → C (h i 1) (λ j → h i j) in
  `(coe 0 1 <i> (@ ty i) d)

let J/eq
  (A : type) (a : A)
  (C : (x : A) (p : Path A a x) → type) (d : C a (λ _ → a))
  : Path (C a _) (J _ _ C d _ (λ _ → a)) d
  =
  let square : `(# <i j> A) =
    λ i j →
      `(hcom 0 j A a [i=0 <_> a] [i=1 <_> a])
  in
  let cube : `(# <i j k> A) =
    λ i j k →
      `(hcom 0 j A a
        [k=0 <j> (@ square i j)]
        [k=1 <_> a]
        [i=0 <_> a]
        [i=1 <_> a])
  in
  λ k →
    `(com 0 1
      <i> (C (@ cube i 1 k) (λ <j> (@ cube i j k)))
      d
      [k=0 <i> (coe 0 i <j> (C (@ square j 1) (λ <k> (@ square j k))) d)]
      [k=1 <_> d])

