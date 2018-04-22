(:> 
 (-> 
  [f : (-> bool bool)]
  [g : (-> bool bool)]
  [p : 
   (-> 
    [b : bool] 
    (# [i] 
     bool 
     [i=0 (f b)] 
     [i=1 (g b)]))]
  (# [i]
   (-> bool bool)
   [i=0 f]
   [i=1 g]))
 
 (lam [f] [g] [p] [i] [x]
  (@ (p x) i)))