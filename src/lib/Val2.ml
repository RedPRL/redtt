module D = DimVal

type tm = Tm.chk Tm.t
type dim = D.t
type query = Eq of dim * dim

type can = [`Can]
type neu = [`Can]

module type Sem =
sig
  include Monad.S
  val ask : dim -> dim -> (D.compare -> 'a m) -> 'a m
  val restrict : dim -> dim -> 'a m -> 'a m
  val fresh : Symbol.t m
end

module V (M : Sem) =
struct

  type 'a cmd = 'a M.m

  module Notation = Monad.Notation (M)
  open Notation

  type _ val_ =
    | Pi : {dom : can val_ cmd; cod : clo cmd} -> can val_
    | V : {dim : dim; ty0 : can val_ cmd; ty1 : can val_ cmd; equiv : can val_ cmd} -> can val_
    | VIn : dim * can val_ * can val_ -> can val_

    | Coe : {dim0 : dim; dim1 : dim; ty : Symbol.t * can val_; el : can val_} -> can val_

    | Lam : clo -> can val_
    | Pair : can val_ * can val_ -> can val_
    | FunApp : neu val_ * can val_ -> can val_
    | ExtApp : neu val_ * dim -> can val_

  and clo = tm * env
  and env = can val_ list

  let car : can val_ -> can val_ cmd = failwith ""
  let cdr : can val_ -> can val_ cmd  = failwith ""

  let apply : can val_ -> can val_ -> can val_ cmd = failwith ""

  let rec coe r r' (x, ty) el =
    M.ask r r' @@ function
    | Same ->
      M.ret el

    | _ ->
      match ty with
      | V vinfo ->
        begin
          M.ask vinfo.dim (D.Fresh x) @@ function
          | D.Same ->
            begin
              M.ask r D.Dim1 @@ function
              | D.Same ->
                M.restrict r' (D.Fresh x) vinfo.equiv >>= fun equiv_r' ->
                vinfo.ty1 >>= fun tyb ->
                coe D.Dim1 r' (x, tyb) el >>= fun coe1r'bn ->
                cdr equiv_r' >>= fun cdr_equiv_r' ->
                apply cdr_equiv_r' coe1r'bn >>= fun app_cdr_equiv ->
                car app_cdr_equiv >>= fun otm ->
                car otm >>= fun otm0 ->
                M.ret @@ VIn (r', otm0, failwith "")

              | _ ->
                failwith "TODO"
            end
          | _ ->
            failwith ""
        end

      | _ ->
        failwith "TODO"

end
