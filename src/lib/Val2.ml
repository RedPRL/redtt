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

  type _ t =
    | Pi : {dom : can t cmd; cod : clo} -> can t
    | V : {dim : dim; ty0 : can t cmd; ty1 : can t cmd; equiv : can t cmd} -> can t
    | VIn : dim * can t * can t -> can t

    | Coe : {dim0 : dim; dim1 : dim; ty : Symbol.t * can t; el : can t} -> can t

    | Lam : clo -> can t
    | Pair : can t * can t -> can t
    | FunApp : neu t * can t -> can t
    | ExtApp : neu t * dim -> can t

  and clo = tm * env
  and env = can t list


  let swap d0 d1 v =
    failwith "TODO"

  let car : can t -> can t cmd = failwith ""
  let cdr : can t -> can t cmd  = failwith ""

  let rec eval : type a. env -> a Tm.t -> can t cmd =
    fun _ _ ->
      failwith "TODO"

  and inst_clo (tm, env) arg =
    eval (arg :: env) tm

  and apply : can t -> can t -> can t cmd =
    fun vfun varg ->
      match vfun with
      | Lam clo ->
        inst_clo clo varg

      | Coe {dim0; dim1; ty = (x, ty); el} ->
        begin
          match ty with
          | Pi {dom; cod} ->
            dom >>= fun vdom ->
            coe dim1 dim0 (x, vdom) varg >>= fun coe_arg0 ->
            M.fresh >>= fun y ->
            coe dim1 (D.Named y) (y, swap x y vdom) varg >>= fun coe_argx ->
            inst_clo cod coe_argx >>= fun codcoe ->
            apply el coe_arg0 >>= fun el' ->
            coe dim0 dim1 (x, codcoe) el'

          | _ ->
            failwith "expected pi"
        end

      | _ ->
        failwith "TODO"

  and coe r r' (x, (ty : can t)) el =
    M.ask r r' @@ function
    | Same ->
      M.ret el

    | _ ->
      match ty with
      | Pi _ ->
        M.ret @@ Coe {dim0 = r; dim1 = r'; ty = (x, ty); el}

      | V vinfo ->
        begin
          M.ask vinfo.dim (D.Named x) @@ function
          | D.Same ->
            begin
              M.ask r D.Dim1 @@ function
              | D.Same ->
                M.restrict r' (D.Named x) vinfo.equiv >>= fun equiv_r' ->
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
