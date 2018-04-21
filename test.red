// below is notation for a type annotation
(:>
 (->
  [ty : (U 0)]
  [p : (# [_] ty)] // this is a "line type" (empty extension type)
  // below is notation for extension types
  (# [i] 
   (ty 
    [i=0 (@ p 1)] 
    [i=1 (@ p 0)])))
 
 (lam [ty] [p] 
  (hcom 0 1 ty (@ p 0)
   [x=0 [y] (@ p y)]
   [x=1 [_] (@ p 0)])))