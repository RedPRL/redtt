(define funext
  [A : (U 0)]
  [B : (-> A (U 0))]
  [f : (-> [x : A] (B x))]
  [g : (-> [x : A] (B x))]
  [p : (-> [x : A] (# [i] (B x) [i=0 (f x)] [i=1 (g x)]))]
  (# [i] (-> [x : A] (B x)) [i=0 f] [i=1 g])
  :>

  (lam [i] [x] (@ (p x) i)))

(define foo bool :>
 tt)

(define bar (# [i] bool [i=0 tt] [i=1 foo]) :>
 (lam [i] tt))