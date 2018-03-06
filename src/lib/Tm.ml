type 'a b = B of 'a

type chk =
  | Up of inf
  | Unit
  | Bool
  | Pi of chk * chk b
  | Sg of chk * chk b
  | Eq of chk b * chk * chk
  | Lam of chk b
  | Pair of chk * chk
  | Ax
  | Tt
  | Ff
  | Dim0
  | Dim1
  | U
  | ChkSub of chk * sub

and inf =
  | Var
  | App of inf * chk
  | Proj1 of inf
  | Proj2 of inf
  | If of chk b * inf * chk * chk
  | Down of chk * chk
  | InfSub of inf * sub

and sub =
  | Id
  | Wk
  | Cmp of sub * sub
  | Ext of sub * chk

let rec weak n =
  match n with
  | 0 -> Wk
  | n -> Cmp (weak (n - 1), Wk)

let var i =
  match i with
  | 0 -> Var
  | n -> InfSub (Var, weak (n - 1))

let rec pp_chk fmt t = 
  match t with 
  | Up t -> Format.fprintf fmt "(up %a)" pp_inf t
  | Unit -> Format.fprintf fmt "unit"
  | Bool -> Format.fprintf fmt "bool"
  | Pi (dom, B cod) -> Format.fprintf fmt "(-> %a [] %a)" pp_chk dom pp_chk cod
  | Sg (dom, B cod) -> Format.fprintf fmt "(* %a [] %a)" pp_chk dom pp_chk cod
  | Eq (B cod, t1, t2) -> Format.fprintf fmt "(eq [] %a %a %a)" pp_chk cod pp_chk t1 pp_chk t2
  | Lam (B t) -> Format.fprintf fmt "(lam [] %a)" pp_chk t
  | _ -> failwith ""

and pp_inf fmt r =
  match r with
  | Var -> Format.fprintf fmt "var"
  | App (r, t) -> Format.fprintf fmt "(app %a %a)" pp_inf r pp_chk t
  | Proj1 r -> Format.fprintf fmt "(car %a)" pp_inf r
  | Proj2 r -> Format.fprintf fmt "(cdr %a)" pp_inf r
  | If (B mot, r, t1, t2) -> Format.fprintf fmt "(if [] %a %a %a %a)" pp_chk mot pp_inf r pp_chk t1 pp_chk t2
  | _ -> failwith ""

let rec equal_chk t1 t2 = failwith ""