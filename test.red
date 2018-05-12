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

