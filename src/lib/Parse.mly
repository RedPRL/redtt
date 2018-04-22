%{
  module TmUtil = TmUtil.Make(struct exception Error = Error end)
  open TmUtil

  module R = ResEnv
%}

%token <int> NUMERAL
%token <string> ATOM
%token LSQ RSQ LPR RPR
%token COLON COLON_ANGLE
%token EQUALS
%token RIGHT_ARROW
%token STAR HASH AT
%token BOOL UNIV LAM CONS CAR CDR TT FF
%token EOF

%start <(ResEnv.t -> Tm.inf Tm.t) option> prog
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
    { fun env ->
        make_node $startpos $endpos @@ Tm.Bool }
  | TT
    { fun env ->
        make_node $startpos $endpos @@ Tm.Tt }

  | FF
    { fun env ->
        make_node $startpos $endpos @@ Tm.Ff }

  | i = NUMERAL
    { fun _ ->
        make_dim_const $startpos $endpos i }

  | LPR; UNIV; i = NUMERAL; RPR
    { fun env ->
        make_node $startpos $endpos @@
        Tm.Univ (Lvl.Const i) }

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
        make_node $startpos $endpos @@
        Tm.Cons (e0 env, e1 env) }

  | e = inf
    { fun env ->
        make_node $startpos $endpos @@
        Tm.Up (e env) }

  ;

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

  | LPR; COLON_ANGLE; ty = chk; tm = chk; RPR
    { fun env ->
        make_node $startpos $endpos @@
        Tm.Down {ty = ty env; tm = tm env} }