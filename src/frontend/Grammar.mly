%{
  open RedTT_Core
  open TmUtil
  open RedBasis
  open Bwd
  open BwdNotation
  module E = ESig
  module R = ResEnv
%}

%token <int> NUMERAL
%token <string> ATOM
%token <string option> HOLE_NAME
%token LSQ RSQ LPR RPR LGL RGL LBR RBR
%token COLON TRIANGLE_RIGHT COMMA DOT PIPE CARET BANG
%token EQUALS
%token RIGHT_ARROW RRIGHT_ARROW BULLET
%token TIMES HASH AT BACKTICK IN WITH WHERE END DATA
%token DIM TICK LOCK
%token S1 S1_REC NAT_REC ELIM LOOP BASE ZERO SUC POS NEGSUC INT INT_REC NAT BOOL UNIV LAM CONS CAR CDR TT FF IF COMP HCOM COM COE LET DEBUG CALL RESTRICT V VPROJ VIN NEXT PREV FIX DFIX BOX_MODALITY OPEN SHUT
%token OF
%token THEN ELSE
%token IMPORT OPAQUE QUIT
%token TYPE PRE KAN
%token EOF


%start <ESig.esig> esig
%%

edecl:
  | LET; a = ATOM; sch = escheme; EQUALS; tm = eterm
    { E.Define (a, `Transparent, sch, tm) }
  | OPAQUE LET; a = ATOM; sch = escheme; EQUALS; tm = eterm
    { E.Define (a, `Opaque, sch, tm) }
  | DEBUG; f = debug_filter
    { E.Debug f }
  | DATA; dlbl = ATOM; WHERE; option(PIPE); constrs = separated_list(PIPE, desc_constr)
    { let desc = List.map (fun constr -> constr dlbl) constrs in
      E.Data (dlbl, desc) }
  | IMPORT; a = ATOM
    { E.Import a }
  | QUIT
    { E.Quit }

debug_filter:
  | { `All }
  | a = ATOM
    { match a with
      | "all" -> `All
      | "constraints" -> `Constraints
      | _ -> failwith "Invalid debug filter: try 'all' or 'constraints' " }

atomic_eterm:
  | BACKTICK; t = tm
    { E.Quo t }
  | a = HOLE_NAME;
    { E.Hole a }
  | HOLE_NAME; LBR; e = eterm; RBR
    { E.Guess e }
  | TYPE
    { E.Type }
  | LGL; es = separated_list(COMMA, eterm); RGL
    { E.Tuple es }
  | LPR; e = eterm; RPR
    { e }
  | a = ATOM; CARET; k = NUMERAL
    { E.Var (a, k) }
  | a = ATOM;
    { if a = "_" then E.Hope else E.Var (a, 0) }
  | n = NUMERAL;
    { E.Num n }
  | BULLET
    { E.TickConst }
  | BOOL
    { E.Bool }
  | TT
    { E.Tt }
  | FF
    { E.Ff }
  | NAT
    { E.Nat }
  | ZERO
    { E.Zero }
  | INT
    { E.Int }
  | S1
    { E.S1 }
  | BASE
    { E.Base }


eframe:
  | e = atomic_eterm
    { E.App e }
  | BANG
    { E.Open }
  | DOT CAR
    { E.Car }
  | DOT CDR
    { E.Cdr }
  | DOT; n = NUMERAL
    { match n with
      | 0 -> E.Car
      | 1 -> E.Cdr
      | _ -> failwith "Parser: invalid projection" }

eterm:
  | e = atomic_eterm
    { e }
  | e = atomic_eterm; fs = nonempty_list(eframe)
    { E.Cut (e, Bwd.from_list fs) }
  | LAM; xs = list(ATOM); RIGHT_ARROW; e = eterm
    { E.Lam (xs, e)   }
  | LET; name = ATOM; COLON; ty = eterm; EQUALS; tm = eterm; IN; body = eterm
    { E.Let {name; ty = Some ty; tm; body} }
  | LET; name = ATOM; EQUALS; tm = eterm; IN; body = eterm
    { E.Let {name; ty = None; tm; body} }

  | IF; e0 = eterm; THEN; e1 = eterm; ELSE; e2 = eterm
    { E.If (None, e0, e1, e2) }

  | IF; e0 = eterm; IN mot = eterm; THEN; e1 = eterm; ELSE; e2 = eterm
    { E.If (Some mot, e0, e1, e2) }

  | SUC; n = atomic_eterm
    { E.Suc n }

  | ELIM; scrut = eterm; IN; mot = eterm; WITH; option(PIPE); clauses = separated_list(PIPE, eclause); END
    { E.Elim {mot = Some mot; scrut; clauses} }

  | ELIM; scrut = eterm; WITH; option(PIPE); clauses = separated_list(PIPE, eclause); END
    { E.Elim {mot = None; scrut; clauses} }

  | NAT_REC; e0 = eterm; WITH; option(PIPE); ZERO; RRIGHT_ARROW; ez = eterm; PIPE; SUC; LPR; n = ATOM; RRIGHT_ARROW; n_rec = ATOM; RPR; RRIGHT_ARROW; es = eterm; END
    { E.NatRec (None, e0, ez, (n, Some n_rec, es)) }

  | NAT_REC; e0 = eterm; WITH; option(PIPE); ZERO; RRIGHT_ARROW; ez = eterm; PIPE; SUC; n = ATOM; RRIGHT_ARROW; es = eterm; END
    { E.NatRec (None, e0, ez, (n, None, es)) }

  | NAT_REC; e0 = eterm; IN; mot = eterm; WITH; option(PIPE); ZERO; RRIGHT_ARROW; ez = eterm; PIPE; SUC; LPR; n = ATOM; RRIGHT_ARROW; n_rec = ATOM; RPR; RRIGHT_ARROW; es = eterm; END
    { E.NatRec (Some mot, e0, ez, (n, Some n_rec, es)) }

  | NAT_REC; e0 = eterm; IN; mot = eterm; WITH; option(PIPE); ZERO; RRIGHT_ARROW; ez = eterm; PIPE; SUC; n = ATOM; RRIGHT_ARROW; es = eterm; END
    { E.NatRec (Some mot, e0, ez, (n, None, es)) }


  | POS; n = eterm
    { E.Pos n }

  | NEGSUC; n = eterm
    { E.NegSuc n }

  | INT_REC; e0 = eterm; WITH; option(PIPE); POS; np = ATOM; RRIGHT_ARROW; ep = eterm; PIPE; NEGSUC; nn = ATOM; RRIGHT_ARROW; en = eterm; END
    { E.IntRec (None, e0, (np, ep), (nn, en)) }

  | LOOP; r = eterm
    { E.Loop r }

  | S1_REC; e0 = eterm; WITH; option(PIPE); BASE; RRIGHT_ARROW; eb = eterm; PIPE; LOOP; x = ATOM; RRIGHT_ARROW; el = eterm; END
    { E.S1Rec (None, e0, eb, (x, el)) }

  | DFIX; LSQ; r = eterm; RSQ; name = ATOM; COLON; ty = eterm; IN; bdy = eterm
    { E.DFixLine {r; name; ty; bdy} }

  | DFIX; name = ATOM; COLON; ty = eterm; IN; bdy = eterm
    { E.DFixLine {r = E.Num 0; name; ty; bdy} }

  | FIX; LSQ; r = eterm; RSQ; name = ATOM; COLON; ty = eterm; IN; bdy = eterm
    { E.FixLine {r; name; ty; bdy} }

  | FIX; name = ATOM; COLON; ty = eterm; IN; bdy = eterm
    { E.FixLine {r = E.Num 0; name; ty; bdy} }

  | COE; r0 = atomic_eterm; r1 = atomic_eterm; tm= atomic_eterm; IN; fam = eterm
    { E.Coe {r = r0; r' = r1; fam; tm} }

  | COMP; r0 = atomic_eterm; r1 = atomic_eterm; cap = atomic_eterm; WITH; option(PIPE); sys = separated_list(PIPE, eface); END
    { E.HCom {r = r0; r' = r1; cap; sys}}

  | COMP; r0 = atomic_eterm; r1 = atomic_eterm; cap = atomic_eterm; IN; fam = eterm; WITH; option(PIPE); sys = separated_list(PIPE, eface); END
    { E.Com {r = r0; r' = r1; fam; cap; sys}}

  | tele = nonempty_list(etele_cell); RIGHT_ARROW; cod = eterm
    { E.Pi (List.flatten tele, cod) }

  | tele = nonempty_list(etele_cell); TIMES; cod = eterm
    { E.Sg (List.flatten tele, cod) }

  | LSQ; dims = nonempty_list(ATOM); RSQ; ty = eterm; WITH; option(PIPE); sys = separated_list(PIPE, eface); END
    { E.Ext (dims, ty, sys)}

  | RESTRICT; ty = eterm; WITH; option(PIPE); sys = separated_list(PIPE, eface); END
    { E.Rst (ty, sys)}

  | dom = atomic_eterm; RIGHT_ARROW; cod = eterm
    { E.Pi ([`Ty ("_", dom)], cod) }

  | dom = atomic_eterm; TIMES; cod = eterm
    { E.Sg ([`Ty ("_", dom)], cod) }

  | BOX_MODALITY; ty = eterm
    { E.Pi ([`Lock], ty)}

  | SHUT; tm = eterm
    { E.Shut tm }

eclause:
  | lbl = ATOM; pbinds = list(epatbind); RRIGHT_ARROW; bdy = eterm
    { lbl, pbinds, bdy }

epatbind:
  | x = ATOM
    { E.PVar x }
  | LPR; x = ATOM; RRIGHT_ARROW; ih = ATOM; RPR
    { E.PIndVar (x, ih) }

eface:
  | r0 = atomic_eterm; EQUALS; r1 = atomic_eterm; RRIGHT_ARROW; e = eterm
    { r0, r1, e }


escheme:
  | tele = list(etele_cell); COLON; cod = eterm
    { (List.flatten tele, cod) }

etele_cell:
  | LPR; xs = separated_nonempty_list(COMMA, ATOM); COLON; ty = eterm; RPR
    { List.map (fun x -> `Ty (x, ty)) xs }
  | LPR; xs = separated_nonempty_list(COMMA, ATOM); COLON; TICK; RPR
    { List.map (fun x -> `Tick x) xs }
  | LPR; xs = separated_nonempty_list(COMMA, ATOM); COLON; DIM; RPR
    { List.map (fun x -> `I x) xs }
  | DIM
    { [`I "_"] }
  | TICK
    { [`Tick "_"] }
  | LOCK
    { [`Lock] }




desc_constr:
| clbl = ATOM
  { fun _dlbl ->
    clbl, Desc.{params = []; args = []} }

| clbl = ATOM; OF; params = nonempty_list(desc_param); TIMES; args = separated_nonempty_list(TIMES, desc_arg)
  { fun dlbl ->
    clbl, Desc.{params; args = List.map (fun arg -> arg dlbl) args} }

| clbl = ATOM; OF; params = nonempty_list(desc_param)
  { fun _dlbl ->
    clbl, Desc.{params; args = []} }

| clbl = ATOM; OF; args = separated_nonempty_list(TIMES, desc_arg)
  { fun dlbl ->
    clbl, Desc.{params = []; args = List.map (fun arg -> arg dlbl) args} }

%inline
desc_arg:
| self = ATOM
  { fun name ->
      if name = self then Desc.Self else failwith ("Expected " ^ name ^ " but got " ^ self)}

%inline
desc_param:
| LPR; x = ATOM; COLON; ty = eterm; RPR
  { x, ty }



esig:
  | d = edecl; esig = esig
    { d :: esig }
  | EOF
    { [] }










tele_with_env:
  | dom = tm; rest = tele_with_env
    { fun env ->
      let env' = R.bind "_" env in
      let tele, env'' = rest env' in
      TCons (None, dom env, tele), env'' }

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
      make_node $startpos $endpos Tm.Bool }

  | INT
    { fun _env ->
      make_node $startpos $endpos Tm.Int }

  | TT
    { fun _env ->
      make_node $startpos $endpos Tm.Tt }

  | FF
    { fun _env ->
      make_node $startpos $endpos Tm.Ff }

  | BULLET
    { fun _env ->
      make_node $startpos $endpos Tm.TickConst }

  | i = NUMERAL
    { fun _env ->
      make_dim_const $startpos $endpos i }

  | LPR; UNIV; k = kind; i = NUMERAL; RPR
    { fun _env ->
      make_node $startpos $endpos @@
      Tm.Univ {kind = k; lvl = Lvl.Const i} }

  | LPR; V; r = tm; ty0 = tm; ty1 = tm; equiv = tm; RPR
    { fun env ->
      make_node $startpos $endpos @@
      Tm.V {r = r env; ty0 = ty0 env; ty1 = ty1 env; equiv = equiv env} }

  | LPR; VIN; r = tm; tm0 = tm; tm1 = tm; RPR
    { fun env ->
      make_node $startpos $endpos @@
      Tm.VIn {r = r env; tm0 = tm0 env; tm1 = tm1 env} }


  | LPR; RIGHT_ARROW; tele = tele; RPR
    { fun env ->
      pi_from_tele (Some ($startpos, $endpos)) @@ tele env }

  | LPR; TIMES; tele = tele; RPR
    { fun env ->
      sg_from_tele (Some ($startpos, $endpos)) @@ tele env }

  | LPR; HASH; mb = multibind(constrained); RPR
    { fun env ->
      ext_from_multibind $startpos $endpos @@ mb env }

  | LPR; TRIANGLE_RIGHT; ty = bind(tm); RPR
    { fun env ->
      make_node $startpos $endpos @@
      Tm.Later (ty env) }

  | LPR; BOX_MODALITY; ty = tm; RPR
    { fun env ->
      make_node $startpos $endpos @@
      Tm.BoxModality (ty env) }

  | LPR; rst = constrained; RPR
    { fun env ->
      let ty, sys = rst env in
      make_node $startpos $endpos @@
      Tm.Rst {ty; sys} }

  | LPR; LAM; mb = multibind(tm); RPR
    { fun env ->
      lam_from_multibind (Some ($startpos, $endpos)) @@ mb env }

  | LPR; NEXT; bnd = bind(tm); RPR
    { fun env ->
      make_node $startpos $endpos @@
      Tm.Next (bnd env) }

  | LPR; SHUT; tm = tm; RPR
    { fun env ->
      make_node $startpos $endpos @@
      Tm.Shut (tm env) }

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
  | a = ATOM; CARET; k = NUMERAL
    { fun env ->
      match R.get a env with
      | `Ix _ -> failwith "Cannot shift bound variable"
      | `Var r -> Tm.Var {name = r; twin = `Only; ushift = k} }

  | a = ATOM
    { fun env ->
      match R.get a env with
      | `Ix i -> Tm.Ix (i, `Only)
      | `Var r -> Tm.Var {name = r; twin = `Only; ushift = 0} }

  | LPR; HCOM; r0 = tm; r1 = tm; ty = tm; cap = tm; sys = elist(face(dimbind(tm))); RPR
    { fun env ->
      Tm.HCom {r = r0 env; r' = r1 env; ty = ty env; cap = cap env; sys = sys env} }

  | LPR; COM; r0 = tm; r1 = tm; ty = dimbind(tm); cap = tm; sys = elist(face(dimbind(tm))); RPR
    { fun env ->
      Tm.Com {r = r0 env; r' = r1 env; ty = ty env; cap = cap env; sys = sys env} }

  | LPR; COE; r0 = tm; r1 = tm; ty = dimbind(tm); tm = tm; RPR
    { fun env ->
      Tm.Coe {r = r0 env; r' = r1 env; ty = ty env; tm = tm env} }

  | LPR; DFIX; r = tm; ty = tm; bdy = bind(tm); RPR
    { fun env ->
      Tm.DFix {r = r env; ty = ty env; bdy = bdy env} }

  | LPR; COLON; ty = tm; tm = tm; RPR
    { fun env ->
      Tm.Down {ty = ty env; tm = tm env} }

cmd:
  | c = cut
    { fun env ->
      c env }

cut:
  | hd = head
    { fun env ->
      hd env, Emp }

  | LPR; CAR; e = cut; RPR
    { fun env ->
      let hd, fs = e env in
      hd, fs #< Tm.Car }

  | LPR; CDR; e = cut; RPR
    { fun env ->
      let hd, fs = e env in
      hd, fs #< Tm.Cdr }

  | LPR; CALL; e = cut; RPR
    { fun env ->
      let hd, fs = e env in
      hd, fs #< Tm.LblCall }

  | LPR; PREV; t = tm; e = cut; RPR
    { fun env ->
      let hd, fs = e env in
      hd, fs #< (Tm.Prev (t env)) }

  | LPR; OPEN; e = cut; RPR
    { fun env ->
      let hd, fs = e env in
      hd, fs #< Tm.Open }

  | LPR; e = cut; arg0 = tm; rest = elist(tm); RPR
    { fun env ->
      let hd, fs = e env in
      let args = arg0 env :: rest env in
      hd, (fs <>< List.map (fun t -> Tm.FunApp t) args) }

  | LPR; AT; e = cut; args = elist(tm); RPR
    { fun env ->
      let hd, fs = e env in
      hd, fs #< (Tm.ExtApp (args env)) }

  | LPR; IF; mot = bind(tm); scrut = cut; tcase = tm; fcase = tm; RPR
    { fun env ->
      let hd, fs = scrut env in
      hd, fs #< (Tm.If {mot = mot env; tcase = tcase env; fcase = fcase env}) }

  | LPR; VPROJ; r = tm; e = cut; ty0 = tm; ty1 = tm; equiv = tm; RPR
    { fun env ->
      let hd, fs = e env in
      hd, fs #< (Tm.VProj {r = r env; ty0 = ty0 env; ty1 = ty1 env; equiv = equiv env})}
