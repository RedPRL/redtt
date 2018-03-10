type d =
  | Clo of Tm.chk Tm.b * env
  | Up of d * dne
  | Unit
  | Bool
  | Pi of d * d
  | Sg of d * d
  | Eq of d * d * d
  | Interval
  | U of [`Const of int | `Omega]
  | Pair of d * d
  | Ax
  | Tt
  | Ff
  | Dim0
  | Dim1
  | Coe of d * d * int * d * d

and dne =
  | Atom of int
  | App of dne * dnf
  | Proj1 of dne
  | Proj2 of dne
  | If of d * dne * dnf * dnf

and dnf =
  | Down of d * d

and env = d list
