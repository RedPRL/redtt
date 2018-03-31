type ('i, 'a) tube = 'i * 'i * 'a
type ('i, 'a) system = ('i, 'a) tube list

type atm = int
type var = int

type 'a vbnd = VB of 'a
type 'a abnd = AB of 'a

type chk = [`Chk]
type inf = [`Inf]

module Lvl = 
struct
  type t = Omega | Const of int
end

type _ t = 
| ThinAtom : 'a t * inf t Thin.t * Thin.t0 -> 'a t
| ThinVar : 'a t * Thin.t0 -> 'a t

| Atom : atm -> inf t
| Var : var -> inf t
| Car : inf t -> inf t
| Cdr : inf t -> inf t
| App : inf t * chk t -> inf t
| Down : {ty : chk t; tm : chk t} -> inf t
| Coe : chk t * chk t * chk t abnd * chk t -> inf t
| HCom : chk t * chk t * chk t * chk t * (chk t, chk t vbnd) system -> inf t

| Up : inf t -> chk t

| Univ : Lvl.t -> chk t
| Pi : chk t * chk t vbnd -> chk t
| Sg : chk t * chk t vbnd -> chk t
| Ext : chk t * (chk t, chk t) system -> chk t
| Interval : chk t

| Lam : chk t vbnd -> chk t
| Cons : chk t * chk t -> chk t
| Dim0 : chk t
| Dim1 : chk t

let path (VB ty, tm0, tm1) = 
  let tube0 = (Up (Var 0), Dim0, ThinVar (tm0, Thin.skip Thin.id)) in
  let tube1 = (Up (Var 0), Dim1, ThinVar (tm1, Thin.skip Thin.id)) in
  Pi (Interval, VB (Ext (ty, [tube0; tube1])))