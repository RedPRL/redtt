%{
  let make_node start stop con =
    Tm.into_info (start, stop) @@ con

  type tele =
    | TCons of Tm.chk Tm.t * tele
    | TEnd of Tm.chk Tm.t

  type 'a multibind = 
    | MBCons of 'a multibind
    | MBEnd of 'a

  let rec pi_from_tele start stop tele =
    match tele with
    | TEnd ty -> ty
    | TCons (ty, tele) ->
      Tm.into_info (start, stop) @@
      Tm.Pi (ty, Tm.B (pi_from_tele start stop tele))

  let rec sg_from_tele start stop tele =
    match tele with
    | TEnd ty -> ty
    | TCons (ty, tele) ->
      Tm.into_info (start, stop) @@
      Tm.Pi (ty, Tm.B (sg_from_tele start stop tele))

  let rec lam_from_multibind start stop mb =
    match mb with
    | MBEnd bdy -> bdy
    | MBCons mb ->
      Tm.into_info (start, stop) @@
      Tm.Lam (Tm.B (lam_from_multibind start stop mb))

  let rec ext_from_multibind start stop mb = 
    match mb with
    | MBCons (MBEnd (ty, sys)) ->
      Tm.into_info (start, stop) @@
      Tm.Ext (Tm.B (ty, sys))
      
    | MBCons mb ->
      Tm.into_info (start, stop) @@
      Tm.Ext (Tm.B (ext_from_multibind start stop mb, []))

    | MBEnd _ ->
      raise Error


  let rec make_multi_funapp start stop fn rest =
    match rest with
    | [] -> 
      fn
    | arg :: rest ->
      let fn' = make_multi_funapp start stop fn rest in
      make_node start stop @@ Tm.FunApp (fn', arg)

  let rec make_multi_extapp start stop fn rest =
    match rest with
    | [] -> 
      fn
    | arg :: rest ->
      let fn' = make_multi_funapp start stop fn rest in
      make_node start stop @@ Tm.ExtApp (fn', arg)

  module R = PTm.ResEnv
%}

%token <int> NUMERAL
%token <string> ATOM
%token LSQ
%token RSQ
%token LPR
%token RPR
%token COLON COLON_ANGLE
%token EQUALS
%token RIGHT_ARROW
%token STAR HASH AT
%token BOOL UNIV LAM CONS CAR CDR
%token EOF

%start <(PTm.ResEnv.t -> Tm.inf Tm.t) option> prog
%%
prog:
  | e = inf
    { Some e }
  | EOF
    { None }
  ;


tele:
  | dom = chk; rest = tele
    { fun env ->
        TCons (dom env, rest @@ R.bind "_" env) }

  | LSQ; x = ATOM; COLON; dom = chk; RSQ; rest = tele
    { fun env ->
        TCons (dom env, rest @@ R.bind x env) }

  | cod = chk
    { fun env ->
        TEnd (cod env) }
  ;

tube(X):
  | LSQ; r0 = chk; EQUALS; r1 = chk; e = X; RSQ
    { fun env ->
        r0 env, r1 env, Some (e env) }
  ;

bind(X):
  | LSQ; x = ATOM; RSQ; e = X
    { fun env ->
        Tm.B (e @@ R.bind x env) }

multibind(X):
  | e = X
    { fun env ->
        MBEnd (e env) }

  | LSQ; x = ATOM; RSQ; mb = multibind(X)
    { fun env ->
        MBCons (mb @@ R.bind x env) }
  ;

constrained:
  | ty = chk; list(tube(chk))
    { fun env -> failwith "" }

chk:
  | BOOL
    { fun env ->
        make_node $startpos $endpos @@ Tm.Bool }

  | LPR; UNIV; i = NUMERAL; RPR
    { fun env ->
        make_node $startpos $endpos @@ Tm.Univ (Lvl.Const i) }

  | LPR; RIGHT_ARROW; tele = tele; RPR
    { fun env ->
        pi_from_tele $startpos $endpos @@ tele env }

  | LPR; STAR; tele = tele; RPR
    { fun env ->
        sg_from_tele $startpos $endpos @@ tele env }

  | LPR; HASH; mb = multibind(constrained); RPR
    { fun env ->
        ext_from_multibind $startpos $endpos @@ mb env }

  | LPR; LAM; mb = multibind(chk); RPR
    { fun env ->
        lam_from_multibind $startpos $endpos @@ mb env }

  | LPR; CONS; e0 = chk; e1 = chk; RPR 
    { fun env ->
        make_node $startpos $endpos @@ Tm.Cons (e0 env, e1 env) }

  | e = inf
    { fun env ->
        make_node $startpos $endpos @@ Tm.Up (e env) }

  ;

inf:
  | a = ATOM
    { fun env ->
        make_node $startpos $endpos @@ Tm.Var (R.get a env) }

  | LPR; CAR; e = inf
    { fun env ->
        make_node $startpos $endpos @@ Tm.Car (e env)}

  | LPR; CDR; e = inf
    { fun env ->
        make_node $startpos $endpos @@ Tm.Cdr (e env)}

  | LPR; e = inf; arg0 = chk; rest = list(chk); RPR
    { fun env ->
        make_multi_funapp $startpos $endpos (e env) (List.rev @@ arg0 env :: List.map (fun x -> x env) rest) }

  | LPR; AT; e = inf; arg0 = chk; rest = list(chk); RPR
    { fun env ->
        make_multi_extapp $startpos $endpos (e env) (List.rev @@ arg0 env :: List.map (fun x -> x env) rest) }

  | LPR; COLON_ANGLE; ty = chk; tm = chk; RPR
    { fun env ->
        make_node $startpos $endpos @@ Tm.Down {ty = ty env; tm = tm env} }
