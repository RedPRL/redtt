import ntype

data void where

let neg (A : type) : type =
  A → void

let void/prop : IsProp void =
  λ v → elim v []
