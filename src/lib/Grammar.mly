%{
  open TmUtil
  module R = ResEnv
%}

%token <int> NUMERAL
%token <string> ATOM
%token DEFINE
%token LSQ RSQ LPR RPR LGL RGL
%token COLON COLON_ANGLE
%token EQUALS
%token RIGHT_ARROW
%token AST TIMES HASH AT
%token BOOL UNIV LAM CONS CAR CDR TT FF IF HCOM COM COE LET
%token PRE KAN
%token EOF

%start <ResEnv.t -> Decl.t list> prog
%%
prog:
  | LPR; DEFINE; name = ATOM; args = tele_with_env; COLON_ANGLE; body = tm; _rpr = RPR; p = prog
    { fun env ->
      let tele, env_bdy = args env in
      let info = $startpos, $endpos(_rpr) in
      let decl = Decl.Define {name; info; args = tele; body = body env_bdy} in
      let env' = R.bind name env in
      decl :: p env' }
  | EOF
    { fun _env -> [] }

tele_with_env:
  | dom = tm; rest = tele_with_env
    { fun env ->
      let env' = R.bind "_" env in
      let tele, env'' = rest env' in
      TCons (Some "_", dom env, tele), env'' }

  | LSQ; x = ATOM; COLON; dom = tm; RSQ; rest = tele_with_env
    { fun env ->
      let env' = R.bind x env in
      let tele, env'' = rest env' in
      TCons (Some x, dom env, tele), env'' }

  | cod = tm
    { fun env ->
      TEnd (cod env), env }

tele:
  | tl = tele_with_env
    { fun env ->
      fst @@ tl env}

face(X):
  | LSQ; r0 = tm; EQUALS; r1 = tm; e = X; RSQ
    { fun env ->
      r0 env, r1 env, Some (e env) }

bind(X):
  | LSQ; x = ATOM; RSQ; e = X
    { fun env ->
      Tm.B (Some x, e @@ R.bind x env) }

dimbind(X):
  | LGL; x = ATOM; RGL; e = X
    { fun env ->
      Tm.B (Some x, e @@ R.bind x env) }

multibind(X):
  | e = X
    { fun env ->
      MBEnd (e env) }

  | LSQ; x = ATOM; RSQ; mb = multibind(X)
    { fun env ->
      MBConsVar (Some x, mb @@ R.bind x env) }

  | LGL; xs = list(ATOM); RGL; mb = multibind(X)
    { fun env ->
      MBConsDims (List.map (fun x -> Some x) xs, mb @@ R.bindn xs env) }


elist(X):
  | xs = list(X)
    { fun env ->
      List.map (fun x -> x env) xs}

constrained:
  | ty = tm; sys = elist(face(tm))
    { fun env ->
      ty env, sys env }

kind:
  | KAN
    { Kind.Kan }
  | PRE
    { Kind.Pre }
  | { Kind.Kan }

tm:
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

  | LPR; UNIV; k = kind; i = NUMERAL; RPR
    { fun _env ->
      make_node $startpos $endpos @@
      Tm.Univ {kind = k; lvl = Lvl.Const i} }

  | LPR; RIGHT_ARROW; tele = tele; RPR
    { fun env ->
      pi_from_tele (Some ($startpos, $endpos)) @@ tele env }

  | LPR; AST; tele = tele; RPR
    { fun env ->
      sg_from_tele (Some ($startpos, $endpos)) @@ tele env }

  | LPR; TIMES; tele = tele; RPR
    { fun env ->
      sg_from_tele (Some ($startpos, $endpos)) @@ tele env }

  | LPR; HASH; mb = multibind(constrained); RPR
    { fun env ->
      ext_from_multibind $startpos $endpos @@ mb env }

  | LPR; rst = constrained; RPR
    { fun env ->
      let ty, sys = rst env in
      make_node $startpos $endpos @@
      Tm.Rst {ty; sys}}

  | LPR; LAM; mb = multibind(tm); RPR
    { fun env ->
      lam_from_multibind (Some ($startpos, $endpos)) @@ mb env }

  | LPR; CONS; e0 = tm; e1 = tm; RPR
    { fun env ->
      make_node $startpos $endpos @@
      Tm.Cons (e0 env, e1 env) }

  | e = cmd
    { fun env ->
      make_node $startpos $endpos @@
      Tm.Up (e env) }

  | LPR; LET; LSQ; x = ATOM; e0 = cmd; RSQ; e1 = tm; RPR
    { fun env ->
      make_node $startpos $endpos @@
      Tm.Let (e0 env, Tm.B (Some x, e1 @@ R.bind x env))}

head:
  | a = ATOM
    { fun env ->
      Tm.Ix (R.get a env) }
  | LPR; HCOM; r0 = tm; r1 = tm; ty = tm; cap = tm; sys = elist(face(dimbind(tm))); RPR
    { fun env ->
      Tm.HCom {r = r0 env; r' = r1 env; ty = ty env; cap = cap env; sys = sys env} }

  | LPR; COLON_ANGLE; ty = tm; tm = tm; RPR
    { fun env ->
      Tm.Down {ty = ty env; tm = tm env} }

cmd:
  | c = cut
    { fun env ->
      let hd, fs = c env in
      Tm.Cut (hd, List.rev fs) }

cut:
  | hd = head
    { fun env ->
      hd env, [] }

  | LPR; CAR; e = cut; RPR
    { fun env ->
      let hd, fs = e env in
      hd, Tm.Car :: fs }

  | LPR; CDR; e = cut; RPR
    { fun env ->
      let hd, fs = e env in
      hd, Tm.Cdr :: fs }

  | LPR; e = cut; arg0 = tm; rest = elist(tm); RPR
    { fun env ->
      let hd, fs = e env in
      let args = List.rev @@ arg0 env :: rest env in
      hd, List.fold_right (fun t fs -> Tm.FunApp t :: fs) args fs }

  | LPR; AT; e = cut; args = elist(tm); RPR
    { fun env ->
      let hd, fs = e env in
      hd, Tm.ExtApp (args env) :: fs }

  | LPR; IF; mot = bind(tm); scrut = cut; tcase = tm; fcase = tm; RPR
    { fun env ->
      let hd, fs = scrut env in
      hd, Tm.If {mot = mot env; tcase = tcase env; fcase = fcase env} :: fs }
