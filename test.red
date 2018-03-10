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

(: (let (: (U 0) unit) [A] (-> (U 0) [B] (-> (* A B) (* A B))))
   (lam [B] (lam [x] x)))