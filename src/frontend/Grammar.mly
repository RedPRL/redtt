%{
  open RedTT_Core
  open TmUtil
  open RedBasis
  open Bwd
  open BwdNotation
  module E = ESig
  module R = ResEnv

  let eterm pos0 pos1 con =
    E.{con; span = Some (pos0, pos1)}
%}

%token <int> NUMERAL
%token <string> ATOM
%token <string option> HOLE_NAME
%token LSQ RSQ LPR RPR LGL RGL LBR RBR
%token COLON TRIANGLE_RIGHT COMMA DOT PIPE CARET BANG
%token EQUALS
%token RIGHT_ARROW RRIGHT_ARROW BULLET
%token TIMES HASH AT BACKTICK IN WITH WHERE END DATA INTRO
%token DIM TICK LOCK
%token ELIM UNIV LAM PAIR FST SND COMP HCOM COM COE LET DEBUG CALL RESTRICT V VPROJ VIN NEXT PREV FIX DFIX BOX_MODALITY OPEN SHUT
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

  | DATA; dlbl = ATOM;
    params = loption(nonempty_list(desc_param));
    univ_spec = option(preceded(COLON, univ_spec));
    WHERE; option(PIPE);
    constrs = separated_list(PIPE, desc_constr);
    { let desc = List.map (fun constr -> constr dlbl) constrs in
      let kind, lvl =
        match univ_spec with
        | Some (k, l) -> k, l
        | None -> `Kan, `Const 0
      in
      E.Data (dlbl, {params; kind; lvl; constrs = desc}) }

  | IMPORT; a = ATOM
    { E.Import a }
  | QUIT
    { E.Quit }

univ_spec:
  | TYPE; k = kind
    { (k, `Const 0) }
  | TYPE; k = kind; CARET; l = NUMERAL
    { (k, `Const l) }


debug_filter:
  | { `All }
  | a = ATOM
    { match a with
      | "all" -> `All
      | "constraints" -> `Constraints
      | _ -> failwith "Invalid debug filter: try 'all' or 'constraints' " }

atomic_econ:
  | BACKTICK; t = tm
    { E.Quo t }
  | a = HOLE_NAME;
    { E.Hole a }
  | HOLE_NAME; LBR; e = eterm; RBR
    { E.Guess e }
  | spec = univ_spec
    { let k, l = spec in E.Type (k, l) }
  | LGL; es = separated_list(COMMA, eterm); RGL
    { E.Tuple es }
  | LPR; e = eterm; RPR
    { e.con }
  | a = ATOM; CARET; k = NUMERAL
    { E.Var (a, k) }
  | a = ATOM;
    { if a = "_" then E.Hope else E.Var (a, 0) }
  | n = NUMERAL;
    { E.Num n }
  | BULLET
    { E.TickConst }

atomic_eterm:
  | e = atomic_econ
    { eterm $startpos $endpos e }

eframe:
  | e = atomic_eterm
    { E.App e }
  | BANG
    { E.Open }
  | DOT FST
    { E.Car }
  | DOT SND
    { E.Cdr }
  | DOT; n = NUMERAL
    { match n with
      | 0 -> E.Car
      | 1 -> E.Cdr
      | _ -> failwith "Parser: invalid projection" }


block(X):
  | WITH; x = X; END
    { x }
  | LSQ; x = X; RSQ
    { x }

pipe_block(X):
  | x = block(preceded(option(PIPE), separated_list(PIPE, X)))
    { x }

econ:
  | e = atomic_econ
    { e }
  | e = atomic_eterm; fs = nonempty_list(eframe)
    { E.Cut (e, Bwd.from_list fs) }
  | LAM; xs = list(ATOM); RIGHT_ARROW; e = eterm
    { E.Lam (xs, e)   }
  | LET; name = ATOM; COLON; ty = eterm; EQUALS; tm = eterm; IN; body = eterm
    { E.Let {name; ty = Some ty; tm; body} }
  | LET; name = ATOM; EQUALS; tm = eterm; IN; body = eterm
    { E.Let {name; ty = None; tm; body} }

  | ELIM; scrut = eterm; IN; mot = eterm; clauses = pipe_block(eclause)
    { E.Elim {mot = Some mot; scrut; clauses} }

  | ELIM; scrut = eterm; clauses = pipe_block(eclause)
    { E.Elim {mot = None; scrut; clauses} }

  | DFIX; LSQ; r = eterm; RSQ; name = ATOM; COLON; ty = eterm; IN; bdy = eterm
    { E.DFixLine {r; name; ty; bdy} }

  | DFIX; name = ATOM; COLON; ty = eterm; IN; bdy = eterm
    { E.DFixLine {r = {con = E.Num 0; span = None}; name; ty; bdy} }

  | FIX; LSQ; r = eterm; RSQ; name = ATOM; COLON; ty = eterm; IN; bdy = eterm
    { E.FixLine {r; name; ty; bdy} }

  | FIX; name = ATOM; COLON; ty = eterm; IN; bdy = eterm
    { E.FixLine {r = {con = E.Num 0; span = None}; name; ty; bdy} }

  | COE; r0 = atomic_eterm; r1 = atomic_eterm; tm= atomic_eterm; IN; fam = eterm
    { E.Coe {r = r0; r' = r1; fam; tm} }

  | COMP; r0 = atomic_eterm; r1 = atomic_eterm; cap = atomic_eterm; sys = pipe_block(eface)
    { E.HCom {r = r0; r' = r1; cap; sys}}

  | COMP; r0 = atomic_eterm; r1 = atomic_eterm; cap = atomic_eterm; IN; fam = eterm; sys = pipe_block(eface)
    { E.Com {r = r0; r' = r1; fam; cap; sys}}

  | tele = nonempty_list(etele_cell); RIGHT_ARROW; cod = eterm
    { E.Pi (List.flatten tele, cod) }

  | tele = nonempty_list(etele_cell); TIMES; cod = eterm
    { E.Sg (List.flatten tele, cod) }

  | LSQ; dims = nonempty_list(ATOM); RSQ; ty = eterm; sys = pipe_block(eface)
    { E.Ext (dims, ty, sys)}

  | RESTRICT; ty = eterm; sys = pipe_block(eface)
    { E.Rst (ty, sys)}

  | dom = atomic_eterm; RIGHT_ARROW; cod = eterm
    { E.Pi ([`Ty ("_", dom)], cod) }

  | dom = atomic_eterm; TIMES; cod = eterm
    { E.Sg ([`Ty ("_", dom)], cod) }

  | BOX_MODALITY; ty = eterm
    { E.Pi ([`Lock], ty)}

  | SHUT; tm = eterm
    { E.Shut tm }

eterm:
  | e = econ
    { eterm $startpos $endpos e }

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
| clbl = ATOM;
  const_specs = loption(nonempty_list(desc_const_spec));
  rec_specs = loption(nonempty_list(desc_rec_spec));
  extent = desc_extent
  { fun dlbl ->
    let dim_specs, boundary = extent in
    clbl, Desc.{const_specs; rec_specs = List.map (fun spec -> spec dlbl) rec_specs; dim_specs; boundary} }

desc_extent:
  | AT;
    dims = list(ATOM);
    boundary = pipe_block(eface)
    { dims, boundary }
  | { [], [] }



%inline
desc_rec_spec:
| LPR; x = ATOM; COLON; self = ATOM; RPR
  { fun name ->
      if name = self then (x, Desc.Self) else failwith ("Expected " ^ name ^ " but got " ^ self)}

%inline
desc_const_spec:
| LSQ; x = ATOM; COLON; ty = eterm; RSQ
  { x, ty }

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
    { `Kan }
  | PRE
    { `Pre }
  | { `Kan }

tm:
  | BULLET
    { fun _env ->
      make_node $startpos $endpos Tm.TickConst }

  | i = NUMERAL
    { fun _env ->
      make_dim_const $startpos $endpos i }

  | LPR; UNIV; k = kind; i = NUMERAL; RPR
    { fun _env ->
      make_node $startpos $endpos @@
      Tm.Univ {kind = k; lvl = `Const i} }

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

  | LPR; PAIR; e0 = tm; e1 = tm; RPR
    { fun env ->
      make_node $startpos $endpos @@
      Tm.Cons (e0 env, e1 env) }

  | LPR; DATA; dlbl = ATOM; RPR
    { fun _ ->
      make_node $startpos $endpos @@
      Tm.Data {dlbl} }

  | LPR; dlbl = ATOM; DOT; INTRO; clbl = ATOM; es = elist(tm); RPR
    { fun env ->
      make_node $startpos $endpos @@
      Tm.Intro (dlbl, clbl, es env) }

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

  | LPR; FST; e = cut; RPR
    { fun env ->
      let hd, fs = e env in
      hd, fs #< Tm.Car }

  | LPR; SND; e = cut; RPR
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

  | LPR; VPROJ; r = tm; e = cut; ty0 = tm; ty1 = tm; equiv = tm; RPR
    { fun env ->
      let hd, fs = e env in
      hd, fs #< (Tm.VProj {r = r env; ty0 = ty0 env; ty1 = ty1 env; equiv = equiv env})}
