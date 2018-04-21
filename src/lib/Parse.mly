%{
  let make_node start stop con =
    Tm.into_info (start, stop) @@ con

  type tele =
    | TCons of Tm.chk Tm.t * tele
    | TEnd of Tm.chk Tm.t

  type multibind = 
    | MBCons of multibind
    | MBEnd of Tm.chk Tm.t

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


  module R = PTm.ResEnv
%}

%token <int> NUMERAL
%token <string> ATOM
%token LEFT_SQUARE
%token RIGHT_SQUARE
%token LEFT_PAREN
%token RIGHT_PAREN
%token COLON
%token EQUALS
%token RIGHT_ARROW
%token STAR HASH
%token BOOL UNIV LAM
%token EOF

%start <(PTm.ResEnv.t -> Tm.inf Tm.t) option> prog
%%
prog:
  | e = inf
    { Some e }
  | EOF
    { None }
  ;


inf:
  | a = ATOM
    { fun env ->
        make_node $startpos $endpos @@ Tm.Var (R.get a env) }

  | LEFT_PAREN; COLON; ty = chk; tm = chk; RIGHT_PAREN
    { fun env ->
        make_node $startpos $endpos @@ Tm.Down {ty = ty env; tm = tm env} }

tele:
  | dom = chk; rest = tele
    { fun env ->
        TCons (dom env, rest @@ R.bind "_" env) }

  | LEFT_SQUARE; x = ATOM; COLON; dom = chk; RIGHT_SQUARE; rest = tele
    { fun env ->
        TCons (dom env, rest @@ R.bind x env) }

  | cod = chk
    { fun env ->
        TEnd (cod env) }
  ;

tube:
  | LEFT_SQUARE; r0 = chk; EQUALS; r1 = chk; e = chk; RIGHT_SQUARE
    { fun env ->
        r0 env, r1 env, e env }
  ;

multibind:
  | e = chk
    { fun env ->
        MBEnd (e env) }

  | LEFT_SQUARE; x = ATOM; RIGHT_SQUARE; mb = multibind
    { fun env ->
        MBCons (mb @@ R.bind x env) }
  ;

chk:
  | BOOL
    { fun env ->
        make_node $startpos $endpos @@ Tm.Bool }

  | LEFT_PAREN; UNIV; i = NUMERAL; RIGHT_PAREN
    { fun env ->
        make_node $startpos $endpos @@ Tm.Univ (Lvl.Const i) }

  | LEFT_PAREN; RIGHT_ARROW; tele = tele; RIGHT_PAREN
    { fun env ->
        pi_from_tele $startpos $endpos @@ tele env }

  | LEFT_PAREN; STAR; tele = tele; RIGHT_PAREN
    { fun env ->
        sg_from_tele $startpos $endpos @@ tele env }

  | LEFT_PAREN; LAM; mb = multibind; RIGHT_PAREN
    { fun env ->
        lam_from_multibind $startpos $endpos @@ mb env }

  | e = inf
    { fun env ->
        make_node $startpos $endpos @@ Tm.Up (e env) }

  ;