import path

let singleton (A : type) (M : A) : `(U pre 0) =
  `(A [0=0 M])

let connection/or
 (A : type)
 (a : A)
 (b : A)
 (p : Path A a b)
 : `(# <i j> A [j=0 (@ p i)] [i=0 (@ p j)] [j=1 b] [i=1 b])
 =
 λ i j →
  ; this is an example of something that is much nicer here than in redprl and yacctt.
  ; we can define using line types all the faces of the composition at once.
  ; definitional equivalence kicks in to make this work.
  let face : `(# <_ _> A) =
    λ k l →
      `(hcom 0 l A (@ p k) [k=0 <w> (@ p w)] [k=1 <_> b])
  in
  `(hcom 1 0 A b
    [i=0 <k> (@ face k j)]
    [i=1 <k> (@ face k 1)]
    [j=0 <k> (@ face k i)]
    [j=1 <k> (@ face k 1)]
    [i=j <k> (@ face k i)])

; an example of using the singleton type to establish an exact equality
let connection/or/diagonal
 (A : type)
 (a : A)
 (b : A)
 (p : Path A a b)
 : singleton (Path A a b) p
 =
 λ i →
   connection/or A a b p i i

let connection/and
 (A : type)
 (a : A)
 (b : A)
 (p : Path A a b)
 : `(# <i j> A [j=0 a] [i=0 a] [j=1 (@ p i)] [i=1 (@ p j)])
 =
 λ i j →
   let face : `(# <_ _> A) =
     λ k l →
     `(hcom 1 l A (@ p k) [k=0 <_> a] [k=1 <m> (@ p m)])
   in
   `(hcom 0 1 A a
     [i=0 <k> (@ face k 0)]
     [i=1 <k> (@ face k j)]
     [j=0 <k> (@ face k 0)]
     [j=1 <k> (@ face k i)]
     [i=j <k> (@ face k i)])


