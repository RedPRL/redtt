(define Path [A : (U 0)] [M : A] [N : A] (U 0) ▷
 (# <i> A [i=0 M] [i=1 N]))

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
