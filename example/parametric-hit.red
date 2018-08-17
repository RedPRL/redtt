import bool
import path

data trunc (A : type) where
| pt [x : A]
| sq (x : trunc) (y : trunc) @ i
  [ i=0 ⇒ x
  | i=1 ⇒ y
  ]

data sum (A : type) (B : type) where
| inl [x : A]
| inr [x : B]


