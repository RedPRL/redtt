module D = DimVal

type tm = Tm.chk Tm.t
type dim = D.t
type query = Eq of dim * dim

type can = [`Can]
type neu = [`Can]

module type Sem =
sig
  include Monad.S

  type state
  val save : state m
  val restore : state -> 'a m -> 'a m

  module Dim :
  sig
    val ask : dim -> dim -> (D.compare -> 'a m) -> 'a m
    val restrict : dim -> dim -> 'a m -> 'a m
    val fresh : Symbol.t m
  end
end

type atom = Symbol.t

module type Perm =
sig
  type t
  val emp : t
  val swap : atom -> atom -> t
  val cmp : t -> t -> t
  val lookup : atom -> t -> atom
  val read : dim -> t -> dim
end

module V (M : Sem) (P : Perm) =
struct

  type 'a cmd = 'a M.m

  module Notation = Monad.Notation (M)
  open Notation

  type perm = P.t

  type _ t =
    | Pi : {dom : can t; cod : clo} -> can t

    | V : {r : dim; ty0 : can t cmd; ty1 : can t cmd; equiv : can t cmd} -> can t
    | VIn : dim * can t * can t -> can t

    | Coe : {r : dim; r' : dim; abs : Symbol.t * can t; el : can t} -> can t

    | Lam : clo -> can t
    | Pair : can t * can t -> can t
    | FunApp : neu t * can t -> can t
    | ExtApp : neu t * dim -> can t

  and clo = tm * env * perm * M.state
  and env = can t list


  let rec act pi v =
    match v with
    | Pi {dom; cod} ->
      Pi {dom = act pi dom; cod = act_clo pi cod}

    | V info ->
      let r = P.read info.r pi in
      let ty0 = act_cmd pi info.ty0 in
      let ty1 = act_cmd pi info.ty1 in
      let equiv = act_cmd pi info.equiv in
      V {r; ty0; ty1; equiv}

    | Coe info ->
      let r = P.read info.r pi in
      let r' = P.read info.r' pi in
      let abs = act_abs pi info.abs in
      let el = act pi info.el in
      Coe {r; r'; abs; el}

    | Lam clo ->
      Lam (act_clo pi clo)

    | _ ->
      failwith ""

  and act_cmd pi cmd =
    act pi <$> cmd

  and act_clo pi (tm, env, pi', st) =
    tm, env, P.cmp pi pi', st

  and act_abs pi (x, vx) =
    P.lookup x pi, act pi vx


  let car : can t -> can t cmd = failwith ""
  let cdr : can t -> can t cmd  = failwith ""

  let rec eval : type a. env * perm -> a Tm.t -> can t cmd =
    fun (env, pi) tm ->
      match Tm.out tm with
      | Tm.Pi (dom, Tm.B (_, cod)) ->
        eval (env, pi) dom >>= fun dom ->
        M.save >>= fun st ->
        M.ret @@ Pi {dom; cod = cod, env, pi, st}

      | Tm.FunApp (fn, arg) ->
        eval (env, pi) fn >>= fun fn ->
        eval (env, pi) arg >>= fun arg ->
        apply fn arg

      | _ -> failwith ""

  and inst_clo (tm, env, pi, st) arg =
    M.restore st @@ eval (arg :: env, pi) tm

  and apply : can t -> can t -> can t cmd =
    fun fn arg ->
      match fn with
      | Lam clo ->
        inst_clo clo arg

      | Coe info ->
        let x, ty = info.abs in
        let dom, cod = out_pi ty in
        let do_coe_arg s =
          M.Dim.fresh >>= fun y ->
          rigid_coe info.r' s (y, act (P.swap x y) dom) arg
        in
        do_coe_arg info.r >>= fun coe_arg_r ->
        do_coe_arg (D.Named x) >>= fun coe_arg_x ->
        apply info.el coe_arg_r >>= fun app ->
        inst_clo cod coe_arg_x >>= fun cod_coe ->
        rigid_coe info.r info.r' (x, cod_coe) app

      | _ ->
        failwith "apply"


  and car el =
    failwith "TODO"

  and make_coe dim0 dim1 mty mel =
    M.Dim.ask dim0 dim1 @@ function
    | D.Same ->
      mel
    | _ ->
      mty >>= fun (x, ty) ->
      mel >>= fun el ->
      rigid_coe dim0 dim1 (x, ty) el

  and rigid_coe r r' abs el =
    match abs with
    | _, Pi _ ->
      M.ret @@ Coe {r; r'; abs; el}

    | x, V info ->
      begin
        M.Dim.ask (D.Named x) info.r @@ function
        | D.Same ->
          begin
            M.Dim.ask r D.Dim0 @@ function
            | D.Same ->
              info.ty1 >>= fun vty1 ->
              M.Dim.restrict D.Dim0 (D.Named x) info.equiv >>= fun vequiv0 ->
              car vequiv0 >>= fun vcar ->
              apply vcar el >>= fun vapp ->
              rigid_coe r r' (x, vty1) vapp >>= fun vcoe ->
              M.ret @@ VIn (r', el, vcoe)

            | _ ->
              failwith ""
          end
        | _ ->
          failwith "TODO"
      end

    | _ ->
      failwith "TODO: rigid_coe"

  and out_pi ty =
    match ty with
    | Pi {dom; cod} ->
      dom, cod

    | _ ->
      failwith "out_pi"


    (*
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
        failwith "TODO" *)

  (* and coe r r' (x, (ty : can t)) el =
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
        failwith "TODO" *)

end
