open RedBasis open Bwd open BwdNotation
open RedTT_Core

module C = Contextual
module U = Unify

type location = Log.location

type diagnostic =
  | UserHole of
      {name : string option;
       tele : U.telescope;
       ty : Tm.tm;
       tm : Tm.tm}
  | PrintTerm of
      {ty : Tm.tm;
       tm : Tm.tm}

type 'a m = ('a * (location * diagnostic) bwd) C.m

let optional (m : 'a m) : 'a option m =
  C.bind (C.optional m) @@ function
  | None -> C.ret (None, Emp)
  | Some (a, ds) -> C.ret (Some a, ds)

let ret a =
  C.ret (a, Emp)

let bind m k =
  C.bind m @@ fun (a, w) ->
  C.bind (k a) @@ fun (b, w') ->
  C.ret (b, w <.> w')

let lift m =
  C.bind m ret

let emit l d =
  C.ret ((), Emp #< (l, d))

let normalize_param p =
  let module Notation = Monad.Notation (C) in
  let open Notation in

  C.base_cx >>= fun cx ->
  let normalize_ty ty =
    let vty = Cx.eval cx ty in
    Cx.quote_ty cx vty
  in
  match p with
  | `P ty ->
    C.ret @@ `P (normalize_ty ty)
  | `Def (ty, tm) ->
    let vty = Cx.eval cx ty in
    let ty' = Cx.quote_ty cx vty in
    let el = Cx.eval cx tm in
    let tm' = Cx.quote cx ~ty:vty el in
    C.ret @@ `Def (ty', tm')
  | `Tw (ty0, ty1) ->
    C.ret @@ `Tw (normalize_ty ty0, normalize_ty ty1)
  | (`I | `NullaryExt | `Tick | `KillFromTick _) as p ->
    C.ret p
  | `R (r0, r1) ->
    C.ret @@ `R (r0, r1)

let rec normalize_tele =
  let module Notation = Monad.Notation (C) in
  let open Notation in
  function
  | [] -> C.ret []
  | (x, p) :: tele ->
    normalize_param p >>= fun p ->
    C.in_scope x p (normalize_tele tele) >>= fun psi ->
    C.ret @@ (x,p) :: psi

let print_diagnostic =
  function
  | (loc, PrintTerm {tm; ty}) ->
    let pp fmt () =
      Format.fprintf fmt "@[<v>%a@,@,has type@,@,%a@]" Tm.pp0 tm Tm.pp0 ty
    in
    Log.pp_message ~loc ~lvl:`Info pp Format.std_formatter ();
    C.ret ()

  | (loc, UserHole {name; tele; ty; _}) ->
    C.local (fun _ -> tele) @@
    begin
      C.bind C.base_cx @@ fun cx ->
      C.bind (normalize_tele @@ Bwd.to_list tele) @@ fun tele ->
      let vty = Cx.eval cx ty in
      let ty = Cx.quote_ty cx vty in

      let pp_restriction fmt =
        let pp_bdy fmt =
          function
          | None -> Format.fprintf fmt "-"
          | Some tm -> Tm.pp0 fmt tm
        in
        let pp_face fmt (r, r', otm) =
          Format.fprintf fmt "%a = %a %a @[%a@]"
            Tm.pp0 r
            Tm.pp0 r'
            Uuseg_string.pp_utf_8 "⇒"
            pp_bdy otm
        in
        Format.pp_print_list ~pp_sep:Format.pp_print_cut pp_face fmt
      in

      let pp_restricted_ty fmt (ty, sys) =
        match sys with
        | [] -> Tm.pp0 fmt ty
        | _ ->
          Format.fprintf fmt "%a@,@,with the following faces:@,@,   @[<v>%a@]"
            Tm.pp0 ty
            pp_restriction sys
      in

      let ty, sys =
        match Tm.unleash ty with
        | Tm.Ext (Tm.NB (Emp, (ty, sys))) ->
          ty, sys
        | _ ->
          ty, []
      in
      let pp fmt () =
        Format.fprintf fmt "@[<v>?%s:@; @[<v>%a@]@,@[<v>%a %a@]@]"
          (match name with Some name -> name | None -> "Hole")
          Dev.pp_params (Bwd.from_list tele)
          Uuseg_string.pp_utf_8 "⊢"
          pp_restricted_ty (ty, sys)
      in
      Log.pp_message ~loc ~lvl:`Info pp Format.std_formatter ();
      C.ret ()
    end

let rec print_diagnostics =
  function
  | Emp ->
    C.ret ()
  | Snoc (w, d) ->
    C.bind (print_diagnostics w) @@ fun _ ->
    print_diagnostic d

let report (m : 'a m) : 'a m =
  C.bind m @@ fun (a, w) ->
  C.bind (C.dump_state Format.err_formatter "Unsolved:" `Unsolved) @@ fun _ ->
  C.bind (print_diagnostics w) @@ fun _ ->
  ret a


let under_restriction r r' (m : 'a m) : 'a option m =
  C.bind (C.under_restriction r r' m) @@ function
  | None ->
    ret None
  | Some (x, ds) ->
    C.ret (Some x, ds)

let in_scopes = C.in_scopes
let in_scope = C.in_scope
let isolate = C.isolate
let unify = lift @@ C.bind C.go_to_top @@ fun _ -> C.local (fun _ -> Emp) U.ambulando
let local = C.local


let run m =
  fst @@ C.run m
