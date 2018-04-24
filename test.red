(define Path [A : (U 0)] [M : A] [N : A] (U 0) :>
 (# [i] A [i = 0 M] [i = 1 N]))

(define funext
 [A : (U 0)]
 [B : (-> A (U 0))]
 [f : (-> [x : A] (B x))]
 [g : (-> [x : A] (B x))]
 [p : (-> [x : A] (Path (B x) (f x) (g x)))]
 (Path (-> [x : A] (B x)) f g)
 :>
 (lam [i] [x] (@ (p x) i)))


(define not [x : bool] bool :>
 (if [_] bool x ff tt))

(define id [A : (U 0)] [x : A] A :>
 x)

(define notnot [x : bool] bool :>
 (not (not x)))

(define notnot/id/pt [x : bool] (Path bool (notnot x) x) :>
 (if
  [x] (Path bool (notnot x) x)
  x
  (lam [i] tt)
  (lam [i] ff)))

(define notnot/id (Path (-> bool bool) notnot (id bool)) :>
 (lam [i] [x]
  (@ (notnot/id/pt x) i)))

(define symm
 [A : (U 0)]
 [p : (# [i] A)]
 (Path A (@ p 1) (@ p 0))
 :>
 (lam [i]
  (hcom 0 1 A (@ p 0)
   [i = 0 [j] (@ p j)]
   [i = 1 [_] (@ p 0)])))


(define trans
 [A : (U 0)]
 [x : A]
 [p : (# [i] A)]
 [q : (Path A (@ p 1) x)]
 (Path A (@ p 0) (@ q 1))
 :>
 (lam [i]
  (hcom 0 1 A (@ p i)
   [i = 0 [_] (@ p 0)]
   [i = 1 [j] (@ q j)])))
