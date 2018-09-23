open RedTT_Core

type var = [`Neg of Name.t | `Pos of Name.t]

(* A one-sided L calculus. *)
type term =
  | Var of var
  | Mu of var * cmd
  | MuTp of cmd

  | Thunk of term
  | MuThunk of Name.t * cmd

  | Tuple of term record
  | Split of Name.t record * cmd

  | Choose of term labeled
  | Case of (Name.t * cmd) record

  | Tp

and 'a labeled = string * 'a
and 'a record = 'a labeled list

and cmd = term * term

let pp_mu fmt () = Uuseg_string.pp_utf_8 fmt "μ"

let pp_tuple pp fmt tuple =
  let pp_sep fmt () = Format.fprintf fmt "@ " in
  let pp_cell fmt (lbl, a) =
    Format.fprintf fmt "[%a %a]"
      Uuseg_string.pp_utf_8 lbl
      pp a
  in
  Format.pp_print_list ~pp_sep pp_cell fmt tuple


let rec pp_term fmt =
  function
  | Var (`Neg x | `Pos x) ->
    Name.pp fmt x
  | Mu (`Neg alpha, cmd) ->
    Format.fprintf fmt
      "@[<hv1>(%a- [%a]@ %a)@]"
      pp_mu ()
      Name.pp alpha
      pp_cmd cmd
  | Mu (`Pos x, cmd) ->
    Format.fprintf fmt
      "@[<hv1>(%a+ [%a]@ %a)@]"
      pp_mu ()
      Name.pp x
      pp_cmd cmd
  | MuTp cmd ->
    Format.fprintf fmt
      "@[<hv1>(%a<tp>@ %a)@]"
      pp_mu ()
      pp_cmd cmd
  | Thunk t ->
    Format.fprintf fmt
      "@[<hv1>{%a}@]"
      pp_term t
  | MuThunk (x, cmd) ->
    Format.fprintf fmt
      "@[<hv1>(%a {%a}@ %a)@]"
      pp_mu ()
      Name.pp x
      pp_cmd cmd
  | Split (xs, cmd) ->
    Format.fprintf fmt
      "@[<hv1>(split @[%a@]@ %a)@]"
      (pp_tuple Name.pp) xs
      pp_cmd cmd
  | Tuple tuple ->
    Format.fprintf fmt
      "@[<hv1>(%a)@]"
      (pp_tuple pp_term) tuple
  | Choose (lbl, term) ->
    Format.fprintf fmt "@[<hv1>%a@ %a@]"
      Uuseg_string.pp_utf_8 lbl
      pp_term term
  | Case branches ->
    let pp_branch fmt (x, cmd) =
      Format.fprintf fmt "[%a] %a"
        Name.pp x
        pp_cmd cmd
    in
    Format.fprintf fmt "@[<hv1>(case@ %a)@]"
      (pp_tuple pp_branch) branches

  | Tp ->
    Format.fprintf fmt "tp"

and pp_cmd fmt (tm0, tm1) =
  Format.fprintf fmt
    "@[<hv1>(cut@ %a@ %a)@]"
    pp_term tm0
    pp_term tm1



module Macro =
struct
  let pmu nm f =
    let x = Name.named @@ Some nm in
    Mu (`Pos x, f x)

  let nmu nm f =
    let x = Name.named @@ Some nm in
    Mu (`Neg x, f x)

  let app_ctx t u =
    let alpha = Name.fresh () in
    let x = Name.fresh () in
    let pair = Tuple ["in", Var (`Pos x); "out", u] in
    let cmd = t, Mu (`Pos x, (Var (`Neg alpha), pair)) in
    MuThunk (alpha, cmd)

  let app t u =
    let alpha = Name.fresh () in
    let cmd = t, app_ctx u (Var (`Neg alpha)) in
    Mu (`Neg alpha, cmd)

  let lambda nm f =
    let x = Name.named @@ Some nm in
    let alpha = Name.fresh () in
    let binders = ["in", x; "out", alpha] in
    let cmd = f x, Var (`Neg alpha) in
    Thunk (Split (binders, cmd))

  let pair t0 t1 =
    let alpha = Name.fresh () in
    let x = Name.fresh () in
    let y = Name.fresh () in
    let cmd2 = Tuple ["0", Var (`Pos x); "1", Var (`Pos y)], Var (`Neg alpha) in
    let cmd1 = t1, Mu (`Pos y, cmd2) in
    let cmd0 = t0, Mu (`Pos x, cmd1) in
    Mu (`Neg alpha, cmd0)
end


let is_neg_term =
  function
  | Var (`Neg _) | Split _ | MuThunk _ | Mu (`Pos _, _) | Tp -> true
  | _ -> false

let is_pos_term =
  function
  | Var (`Pos _) | Tuple _ | Thunk _ | Mu (`Neg _, _) | MuTp _ -> true
  | _ -> false

let is_pos_value =
  function
  | Var (`Pos _) | Tuple _ | Thunk _ -> true
  | _ -> false


(* The basic environment machine from Curien-Herbelin 2000. *)
module Machine =
struct
  module Env = Map.Make (Name)

  type env = closure Env.t
  and closure = Clo of term * env

  type state = closure * closure * closure list

  let clo_cmd env (tm0, tm1) stk =
    Clo (tm0, env), Clo (tm1, env), stk

  let load : cmd -> state =
    fun (tm0, tm1) ->
      Clo (tm0, Env.empty),
      Clo (tm1, Env.empty),
      []

  exception Final

  let rec pp_clo fmt =
    function
    | Clo (tm, env) ->
      let cells = Env.bindings env in
      let pp_cell fmt (x, clo) =
        Format.fprintf fmt "%a -> %a" Name.pp x pp_clo clo
      in
      pp_term fmt tm

  let pp_state fmt (clo0, clo1) =
    Format.fprintf fmt "@[<hv1>(cut@ %a@ %a)@]"
      pp_clo clo0
      pp_clo clo1


  let polarity tm =
    if is_neg_term tm then `Neg else if is_pos_term tm then `Pos else
      failwith "Internal error: polarity"

  let orient (state : state) : state =
    let clo0, clo1, stk = state in
    let Clo (tm0, _) = clo0 in
    let Clo (tm1, _) = clo1 in
    match polarity tm0, polarity tm1 with
    | `Neg, `Pos -> clo1, clo0, stk
    | `Pos, `Neg -> clo0, clo1, stk
    | _ ->
      Format.eprintf "tm0: %a@." pp_term tm0;
      Format.eprintf "tm1: %a@." pp_term tm1;
      failwith "orient"



  let step (state : state) : state =
    let clo0, clo1, stk = orient state in
    let Clo (tm0, env0) = clo0 in
    let Clo (tm1, env1) = clo1 in
    match tm0, tm1, stk with
    | Mu (`Neg alpha, cmd), _, _ ->
      let env = Env.add alpha clo1 env0 in
      clo_cmd env cmd stk

    | _, Mu (`Pos x, cmd), _ when is_pos_value tm0 ->
      let env = Env.add x clo0 env1 in
      clo_cmd env cmd stk

    | MuTp cmd, _, _ ->
      clo_cmd env0 cmd @@ clo1 :: stk

    | _, Tp, clo :: stk when is_pos_value tm0 ->
      clo0, clo, stk

    | Tuple tuple, Split (xs, cmd), _ ->
      let alg env (lbl, x) =
        let term = List.assoc lbl tuple in
        Env.add x (Clo (term, env0)) env
      in
      let env = List.fold_left alg env1 xs in
      clo_cmd env cmd stk

    | Thunk term, MuThunk (alpha, cmd), _ ->
      let env = Env.add alpha (Clo (term, env0)) env1 in
      clo_cmd env cmd stk

    | Var (`Pos x), _, _ ->
      Env.find x env0, clo1, stk

    | _, Var (`Neg alpha), _ ->
      clo0, Env.find alpha env1, stk

    | _ ->
      raise Final

  let rec crush =
    function
    | Clo (term, env) ->
      subst env term

  and subst (env : env) =
    function
    | Var (`Pos x) ->
      begin
        try crush @@ Env.find x env with
        | Not_found -> Var (`Pos x)
      end
    | Var (`Neg alpha) ->
      begin
        try crush @@ Env.find alpha env with
        | Not_found -> Var (`Pos alpha)
      end
    | Tuple tuple ->
      let tuple = List.map (fun (lbl, tm) -> lbl, subst env tm) tuple in
      Tuple tuple
    | Tp ->
      Tp
    | Mu (x, cmd) ->
      Mu (x, subst_cmd env cmd)
    | MuTp cmd ->
      MuTp (subst_cmd env cmd)
    | Thunk tm ->
      Thunk (subst env tm)
    | MuThunk (x, cmd) ->
      MuThunk (x, subst_cmd env cmd)
    | Split (xs, cmd) ->
      Split (xs, subst_cmd env cmd)
    | Choose (lbl, tm) ->
      Choose (lbl, subst env tm)
    | Case branches ->
      let branches = List.map (fun (lbl, (x, cmd)) -> lbl, (x, subst_cmd env cmd)) branches in
      Case branches

  and subst_cmd env (tm0, tm1) =
    subst env tm0, subst env tm1


  and unload ((clo0 : closure), (clo1 : closure), stk) =
    let tm0 = crush clo0 in
    let tm1 = crush clo1 in
    let tms = List.map crush stk in
    let rec go cmd =
      function
      | [] -> cmd
      | tm :: tms ->
        let cmd' = MuTp cmd, tm in
        go cmd' tms
    in
    go (tm0, tm1) tms


  let rec execute : state -> state =
    fun state ->
      match step state with
      | state -> execute state
      | exception Final -> state

  let rec debug : state -> state =
    fun state ->
      Format.eprintf "State: %a@." pp_cmd (unload state);
      match step state with
      | state ->
        debug state
      | exception Final ->
        Format.eprintf "Final: %a@." pp_cmd (unload state);
        state
end



let example_cmd =
  let open Macro in
  let null = Tuple [] in
  let f =
    lambda "x" @@ fun x ->
    lambda "y" @@ fun y ->
    pair (Var (`Pos x)) (Var (`Pos y))
  in
  app (app f null) null, Tp

let test () =
  ignore @@ Machine.debug @@ Machine.load example_cmd
