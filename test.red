(define Path [A : (U 0)] [M : A] [N : A] (U 0) :>
 (# [i] A [i=0 M] [i=1 N]))

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


(define notnot [x : bool] bool :>
 (not (not x)))

(define notnotidpt [x : bool] (Path bool (notnot x) x) :>
 (if
  [x] (Path bool (notnot x) x)
  x
  (lam [i] tt)
  (lam [i] ff)))

(define notnotid (Path (-> bool bool) notnot (lam [x] x)) :>
 (lam [i] [x]
  (@ (notnotidpt x) i)))


