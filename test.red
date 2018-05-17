(define Path [A : (U 0)] [M : A] [N : A] (U 0) ▷
 (# <i> A [i=0 M] [i=1 N]))

(define PathP [A : (# <i> (U 0))] [M : (@ A 0)] [N : (@ A 1)] (U 0) ▷
 (# <i> (@ A i) [i=0 M] [i=1 N]))

(define funext
 [A : (U 0)]
 [B : (→ A (U 0))]
 [f : (→ [x : A] (B x))]
 [g : (→ [x : A] (B x))]
 [p : (→ [x : A] (Path (B x) (f x) (g x)))]
 (Path (→ [x : A] (B x)) f g)
 ▷
 (λ <i> [x] (@ (p x) i)))

(define not [x : bool] bool ▷
 (if [_] bool x ff tt))

(define id [A : (U 0)] [x : A] A ▷
 x)

(define not∘not [x : bool] bool ▷
 (not (not x)))

(define not∘not/id/pt [x : bool] (Path bool (not∘not x) x) ▷
 (if
  [x] (Path bool (not∘not x) x)
  x
  (λ <i> tt)
  (λ <i> ff)))

(define not∘not/id (Path (→ bool bool) not∘not (id bool)) ▷
 (λ <i> [x]
  (@ (not∘not/id/pt x) i)))

(define symm
 [A : (U 0)]
 [p : (# <i> A)]
 (Path A (@ p 1) (@ p 0))
 ▷
 (λ <i>
  (hcom 0 1 A (@ p 0)
   [i=0 <j> (@ p j)]
   [i=1 <_> (@ p 0)])))

(define trans
 [A : (U 0)]
 [x : A]
 [p : (# <i> A)]
 [q : (Path A (@ p 1) x)]
 (Path A (@ p 0) (@ q 1))
 ▷
 (λ <i>
  (hcom 0 1 A (@ p i)
   [i=0 <_> (@ p 0)]
   [i=1 <j> (@ q j)])))


(define singleton
 [A : (U 0)]
 [M : A]
 (U pre 0)
 ▷
 (A [0=0 M]))

(define restriction-test
 (singleton bool tt)
 ▷
 tt)

(define _
 (bool [1=1 tt])
 ▷
 restriction-test)

(define _
 [M : (singleton bool tt)]
 bool
 ▷
 M)


(define connection/and
 [A : (U 0)]
 [a : A]
 [b : A]
 [p : (Path A a b)]
 (PathP (λ <i> (Path A a (@ p i))) (λ <_> a) p)
 ▷
 (λ <i> <j>
  (hcom 0 1 A a
   [i=0 <k> (hcom 1 0 A (@ p k) [k=0 <_> a] [k=1 <l> (@ p l)])]
   [i=1 <k> (hcom 1 j A (@ p k) [k=0 <_> a] [k=1 <l> (@ p l)])]
   [j=0 <k> (hcom 1 0 A (@ p k) [k=0 <_> a] [k=1 <l> (@ p l)])]
   [j=1 <k> (hcom 1 i A (@ p k) [k=0 <_> a] [k=1 <l> (@ p l)])]
   [i=j <k> (hcom 1 i A (@ p k) [k=0 <_> a] [k=1 <l> (@ p l)])])))

(define connection/or
 [A : (U 0)]
 [a : A]
 [b : A]
 [p : (Path A a b)]
 (PathP (λ <i> (Path A (@ p i) b)) p (λ <_> b))
 ▷
 (λ <i> <j>
  (hcom 1 0 A b
   [i=0 <k> (hcom 0 j A (@ p k) [k=0 <w> (@ p w)] [k=1 <_> b])]
   [i=1 <k> (hcom 0 1 A (@ p k) [k=0 <w> (@ p w)] [k=1 <_> b])]
   [j=0 <k> (hcom 0 i A (@ p k) [k=0 <w> (@ p w)] [k=1 <_> b])]
   [j=1 <k> (hcom 0 1 A (@ p k) [k=0 <w> (@ p w)] [k=1 <_> b])]
   [i=j <k> (hcom 0 i A (@ p k) [k=0 <w> (@ p w)] [k=1 <_> b])])))

(define connection/or/diagonal
 [A : (U 0)]
 [a : A]
 [b : A]
 [p : (Path A a b)]
 (singleton (Path A a b) p)
 ▷
 (λ <i>
  (@ (@ (connection/or A a b p) i) i)))

(define connection/and/fancy
 [A : (U 0)]
 [a : A]
 [b : A]
 [p : (Path A a b)]
 (# <i j> A [j=0 a] [i=0 a] [j=1 (@ p i)] [i=1 (@ p j)])
  ▷
 (λ <i j>
  (hcom 0 1 A a
   [i=0 <k> (hcom 1 0 A (@ p k) [k=0 <_> a] [k=1 <l> (@ p l)])]
   [i=1 <k> (hcom 1 j A (@ p k) [k=0 <_> a] [k=1 <l> (@ p l)])]
   [j=0 <k> (hcom 1 0 A (@ p k) [k=0 <_> a] [k=1 <l> (@ p l)])]
   [j=1 <k> (hcom 1 i A (@ p k) [k=0 <_> a] [k=1 <l> (@ p l)])]
   [i=j <k> (hcom 1 i A (@ p k) [k=0 <_> a] [k=1 <l> (@ p l)])])))
