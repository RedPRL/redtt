%{
  open TmUtil
  module R = ResEnv
%}

%token <int> NUMERAL
%token <string> ATOM
%token DEFINE
%token LSQ RSQ LPR RPR
%token COLON COLON_ANGLE
%token EQUALS
%token RIGHT_ARROW
%token STAR HASH AT
%token BOOL UNIV LAM CONS CAR CDR TT FF IF HCOM COM COE
%token EOF

%start <ResEnv.t -> Decl.t list> prog
%%
prog:
  | LPR; DEFINE; name = ATOM; args = tele_with_env; COLON_ANGLE; body = chk; _rpr = RPR; p = prog
    { fun env -> 
      let tele, env_bdy = args env in
      let info = $startpos, $endpos(_rpr) in
      let decl = Decl.Define {name; info; args = tele; body = body env_bdy} in
      let env' = R.bind name env in
      decl :: p env' }
  | EOF
    { fun _env -> [] }

tele_with_env:
  | dom = chk; rest = tele_with_env
    { fun env ->
      let env' = R.bind "_" env in
      let tele, env'' = rest env' in
      TCons (Some "_", dom env, tele), env'' }

  | LSQ; x = ATOM; COLON; dom = chk; RSQ; rest = tele_with_env
    { fun env ->
      let env' = R.bind x env in
      let tele, env'' = rest env' in
      TCons (Some x, dom env, tele), env'' }

  | cod = chk
    { fun env ->
      TEnd (cod env), env }

tele:
  | tl = tele_with_env
    { fun env ->
      fst @@ tl env}

tube(X):
  | LSQ; r0 = chk; EQUALS; r1 = chk; e = X; RSQ
    { fun env ->
      r0 env, r1 env, Some (e env) }

bind(X):
  | LSQ; x = ATOM; RSQ; e = X
    { fun env ->
      Tm.B (Some x, e @@ R.bind x env) }

multibind(X):
  | e = X
    { fun env ->
      MBEnd (e env) }

  | LSQ; x = ATOM; RSQ; mb = multibind(X)
    { fun env ->
      MBCons (Some x, mb @@ R.bind x env) }


elist(X):
  | xs = list(X)
    { fun env ->
      List.map (fun x -> x env) xs}

constrained:
  | ty = chk; sys = elist(tube(chk))
    { fun env ->
      ty env, sys env }

chk:
  | BOOL
    { fun _env ->
      make_node $startpos $endpos @@ Tm.Bool }

  | TT
    { fun _env ->
      make_node $startpos $endpos @@ Tm.Tt }

  | FF
    { fun _env ->
      make_node $startpos $endpos @@ Tm.Ff }

  | i = NUMERAL
    { fun _env ->
      make_dim_const $startpos $endpos i }

  | LPR; UNIV; i = NUMERAL; RPR
    { fun _env ->
      make_node $startpos $endpos @@
      Tm.Univ (Lvl.Const i) }

  | LPR; RIGHT_ARROW; tele = tele; RPR
    { fun env ->
      pi_from_tele (Some ($startpos, $endpos)) @@ tele env }

  | LPR; STAR; tele = tele; RPR
    { fun env ->
      sg_from_tele (Some ($startpos, $endpos)) @@ tele env }

  | LPR; HASH; mb = multibind(constrained); RPR
    { fun env ->
      ext_from_multibind $startpos $endpos @@ mb env }

  | LPR; LAM; mb = multibind(chk); RPR
    { fun env ->
      lam_from_multibind (Some ($startpos, $endpos)) @@ mb env }

  | LPR; CONS; e0 = chk; e1 = chk; RPR
    { fun env ->
      make_node $startpos $endpos @@
      Tm.Cons (e0 env, e1 env) }

  | e = inf
    { fun env ->
      make_node $startpos $endpos @@
      Tm.Up (e env) }

inf:
  | a = ATOM
    { fun env ->
      make_node $startpos $endpos @@
      Tm.Var (R.get a env) }

  | LPR; CAR; e = inf
    { fun env ->
      make_node $startpos $endpos @@
      Tm.Car (e env)}

  | LPR; CDR; e = inf
    { fun env ->
      make_node $startpos $endpos @@
      Tm.Cdr (e env)}

  | LPR; e = inf; arg0 = chk; rest = elist(chk); RPR
    { fun env ->
      make_multi_funapp $startpos $endpos (e env) @@
      List.rev @@ arg0 env :: rest env }

  | LPR; AT; e = inf; arg0 = chk; rest = elist(chk); RPR
    { fun env ->
      make_multi_extapp $startpos $endpos (e env) @@
      List.rev @@ arg0 env :: rest env }

  | LPR; IF; mot = bind(chk); scrut = inf; tcase = chk; fcase = chk; RPR 
    { fun env ->
      make_node $startpos $endpos @@ 
      Tm.If {mot = mot env; scrut = scrut env; tcase = tcase env; fcase = fcase env} }

  | LPR; HCOM; dim0 = chk; dim1 = chk; ty = chk; cap = chk; sys = elist(tube(bind(chk))); RPR
    { fun env ->
      make_node $startpos $endpos @@
      Tm.HCom {dim0 = dim0 env; dim1 = dim1 env; ty = ty env; cap = cap env; sys = sys env} }

  | LPR; COLON_ANGLE; ty = chk; tm = chk; RPR
    { fun env ->
      make_node $startpos $endpos @@
      Tm.Down {ty = ty env; tm = tm env} }