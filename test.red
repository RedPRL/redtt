(: unit
  (let
  (: (-> bool bool) (lam [x] (if bool x ff tt)))
  [not]
    (let
      (: (= (-> bool bool) not not) (lam [_] not))
      [_]
        ax)))