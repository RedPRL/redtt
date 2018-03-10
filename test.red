(: unit
  (let
  (: (-> bool bool) (lam [x] (if bool x ff tt)))
  [not]
    (let
      (: (= (-> bool bool) not not) (lam [_] (lam [x] (if bool x ff tt))))
      [_]
        ax)))


(: (-> unit unit)
   (lam [x] x))