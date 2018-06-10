let Path
  [A : type]
  [M : `A]
  [N : `A]
  : type
  ⇒
  `(# <i> A [i=0 M] [i=1 N])

let funext
  [A : type]
  [B : `(→ A (U 0))]
  [f : `(→ [x : A] (B x))]
  [g : `(→ [x : A] (B x))]
  [p : `(→ [x : A] (Path (B x) (f x) (g x)))]
  : `(Path (→ [x : A] (B x)) f g)
  ⇒
  λ i x →
    `(@ (p x) i)


let not [x : `bool] : `bool ⇒
  `(if [_] bool x ff tt)

let id [A : type] [x : `A] : `A ⇒ `x

let not∘not [x : `bool] : `bool ⇒
 `(not (not x))


let not∘not/id/pt [x : `bool] : `(Path bool (not∘not x) x) ⇒
 `(if
   [x] (Path bool (not∘not x) x)
   x
   (λ <i> tt)
   (λ <i> ff))

let not∘not/id : `(Path (→ bool bool) not∘not (id bool)) ⇒
  λ i x →
   `(@ (not∘not/id/pt x) i)

let symm
  [A : type]
  [p : `(# <i> A)]
  : `(Path A (@ p 1) (@ p 0))
  ⇒
  λ i →
   `(hcom 0 1 A (@ p 0)
     [i=0 <j> (@ p j)]
     [i=1 <_> (@ p 0)])

let trans
  [A : type]
  [x : `A]
  [p : `(# <i> A)]
  [q : `(Path A (@ p 1) x)]
  : `(Path A (@ p 0) (@ q 1))
  ⇒
  λ i →
   `(hcom 0 1 A (@ p i)
     [i=0 <_> (@ p 0)]
     [i=1 <j> (@ q j)])

let singleton [A : type] [M : `A] : `(U pre 0) ⇒
  `(A [0=0 M])

let restriction-test : `(singleton bool tt) ⇒ `tt
let _ : `(bool [1=1 tt]) ⇒ `restriction-test
let _ [M : `(singleton bool tt)] : `bool ⇒ `M


let connection/or
 [A : type]
 [a : `A]
 [b : `A]
 [p : `(Path A a b)]
 : `(# <i j> A [j=0 (@ p i)] [i=0 (@ p j)] [j=1 b] [i=1 b])
 ⇒
 λ i j →
  ; this is an example of something that is much nicer here than in redprl and yacctt.
  ; we can define using line types all the faces of the composition at once.
  ; definitional equivalence kicks in to make this work.
  let face : `(# <_ _> A) ⇒
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
 [A : type]
 [a : `A]
 [b : `A]
 [p : `(Path A a b)]
 : `(singleton (Path A a b) p)
 ⇒
 λ i →
  `(@ (connection/or A a b p) i i)

 let connection/and
  [A : type]
  [a : `A]
  [b : `A]
  [p : `(Path A a b)]
  : `(# <i j> A [j=0 a] [i=0 a] [j=1 (@ p i)] [i=1 (@ p j)])
  ⇒
  λ i j →
    let face : `(# <_ _> A) ⇒
      λ k l →
      `(hcom 1 l A (@ p k) [k=0 <_> a] [k=1 <m> (@ p m)])
    in
    `(hcom 0 1 A a
      [i=0 <k> (@ face k 0)]
      [i=1 <k> (@ face k j)]
      [j=0 <k> (@ face k 0)]
      [j=1 <k> (@ face k i)]
      [i=j <k> (@ face k i)])


let foo [x : `(× bool bool)] : `(× bool bool) ⇒
  let z0 : `bool ⇒ `(car x) in
  let z1 : `bool ⇒ `tt in
  < `z0, `z1 >

let testing [x : `(bool [1=1 tt])] : `(singleton bool tt) ⇒
  `x

let hset [A : `(U 0)] : `(U 0) =>
  `(→
    [x : A]
    [y : A]
    [p : (Path A x y)]
    [q : (Path A x y)]
    (Path (Path A x y) p q))


let hset/exponential-ideal
  [A : `(U 0)]
  [B : `(U 0)]
  [hset/B : `(hset B)]
  : `(hset (→ A B))
  =>
  λ f g α β i j x →
    `(@
      (@
       (hset/B
        (f x)
        (g x)
        (λ <k> ((@ α k) x))
        (λ <k> ((@ β k) x)))
       i)
      j)


debug
