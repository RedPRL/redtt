%{
  open RedTT_Core
  open TmUtil
  open RedBasis
  open Bwd
  open BwdNotation
  module E = ML
  module R = ResEnv

  let locate loc con =
    E.{con; span = Some loc}

  let atom_to_econ a =
    if a = "_" then E.Hope else E.Var {name = a; ushift = 0}

  let lost_eterm e : E.eterm =
    E.{con = e; span = None}

  let atom_to_lost_eterm a : E.eterm =
    lost_eterm (atom_to_econ a)

  let atom_to_lost_frame a : E.frame =
    E.App (atom_to_lost_eterm a)

  let lost_frame e : E.frame =
    E.App (lost_eterm e)

  let spine_to_econ (e, es) =
    match es with
    | [] -> e
    | _ -> E.Cut (lost_eterm e, es)
%}

%token <int> NUMERAL
%token <string> ATOM
%token <string> STRING
%token <string option> HOLE_NAME
%token <string list> IMPORT
%token LSQ RSQ LPR RPR LGL RGL LBR RBR LTR RTR LLGL RRGL
%token COLON COMMA SEMI DOT PIPE CARET BOUNDARY BANG
%token EQUALS
%token RIGHT_ARROW RIGHT_TACK
%token TIMES AST HASH AT BACKTICK IN WITH WHERE BEGIN END DATA INTRO
%token DIM
%token ELIM UNIV LAM PAIR FST SND COMP HCOM COM COE LET FUN V VPROJ VIN REFL
%token PUBLIC PRIVATE OPAQUE QUIT DEBUG NORMALIZE DEF PRINT CHECK
%token TYPE PRE KAN
%token META
%token EOF


%start <ML.mlcmd ML.info> mltoplevel
%%

located(X):
  | e = X
    { locate $loc e }

edata_params:
  | params = nonempty_list(etele_cell); RIGHT_TACK;
    { params }
  | { [] }

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
      | "unsolved" -> `Unsolved
      | _ -> failwith "Invalid debug filter: try 'all' or 'constraints' or 'unsolved'" }

eproj:
  | DOT FST
    { E.Fst }
  | DOT SND
    { E.Snd }
  | DOT VPROJ
    { E.VProj }

atom_econ:
  | a = ATOM
    { atom_to_econ a }
  | a = ATOM; CARET; k = NUMERAL
    { E.Var {name = a; ushift = k} }

atomoid_econ:
  | BACKTICK; t = tm
    { E.Quo t }

  | a = HOLE_NAME
    { E.Hole (a, None) }

  | HOLE_NAME; LBR; e = located(econ); RBR
    { E.Guess e }

  | ELIM; scrut = option(located(atomic)); mot = option(preceded(IN,located(econ))); clauses = pipe_block(eclause)
    { match scrut with
    | Some scrut -> E.Elim {mot; scrut; clauses}
    | None -> E.ElimFun {clauses} }

  | spec = univ_spec
    { let k, l = spec in E.Type (k, l) }
  (* in theory this rule can replace the following three, but it seems there's some bug.
  | LPR; es = separated_list(COMMA, located(econ)); RPR
    { E.Tuple es }
  *)
  | LPR; RPR
    { E.Tuple [] }
  | LPR; e = econ; RPR
    { e }
  | LPR; e = located(econ); COMMA; es = separated_nonempty_list(COMMA, located(econ)); RPR
    { E.Tuple (e :: es) }
  | REFL
    { E.Refl }
  | n = NUMERAL;
    { E.Num n }

  | LTR; c = mlcmd; RTR
    { E.RunML c }


atomic:
  | e = atom_econ
    { e }
  | e = atomoid_econ
    { e }

framoid:
  | e = located(atomoid_econ)
    { E.App e }
  | p = eproj
    { p }

framic:
  | e = located(atomic)
    { E.App e }
  | p = eproj
    { p }

app_proj_spine:
  (* a b *)
  | atoms = nonempty_list(ATOM)
    { let head, tail = ListUtil.split_head atoms in
      atom_to_econ head, List.map atom_to_lost_frame tail }
  (* a b c .0 ... *)
  (* a b (e) ... *)
  | atoms = nonempty_list(ATOM); p = framoid; fs = list(framic)
    { let head, medium = ListUtil.split_head atoms in
      atom_to_econ head, List.concat [List.map atom_to_lost_frame medium; [p]; fs] }
  (* a b c^1 ... *)
  | atoms = nonempty_list(ATOM); CARET; k = NUMERAL; fs = list(framic)
    { let atoms, last_atom = ListUtil.split_last atoms in
      let econs = List.append (List.map atom_to_econ atoms) [E.Var {name = last_atom; ushift = k}] in
      let head_econ, middle_econs = ListUtil.split_head econs in
      head_econ, List.append (List.map lost_frame middle_econs) fs }
  | e = atomoid_econ; fs = list(framic)
    { e, fs }

spine_con:
  | ap = app_proj_spine
    { spine_to_econ ap }

  | LSQ; dims = nonempty_list(ATOM); RSQ; ty = located(econ); sys = pipe_block(eface)
    { E.Ext (dims, ty, sys)}

  | COMP; r0 = located(atomic); r1 = located(atomic); cap = located(atomic); sys = pipe_block(eface)
    { E.HCom {r = r0; r' = r1; cap; sys}}

  | COMP; r0 = located(atomic); r1 = located(atomic); cap = located(atomic); IN; fam = located(econ); sys = pipe_block(eface)
    { E.Com {r = r0; r' = r1; fam; cap; sys}}

  | V; x = ATOM; ty0 = located(atomic); ty1 = located(atomic); equiv = located(atomic)
    { E.V {x; ty0; ty1; equiv} }

%inline
block(X):
  | WITH; x = X; END
    { x }
  | LSQ; x = X; RSQ
    { x }

pipe_block(X):
  | x = block(preceded(option(PIPE), separated_list(PIPE, X)))
    { x }

%inline
times_or_ast:
  | TIMES
    {}
  | AST
    {}

econ:
  | e = spine_con
    { e }

  | a = HOLE_NAME; SEMI; e = located(econ)
    { E.Hole (a, Some e) }

  | LAM; xs = list(einvpat); RIGHT_ARROW; e = located(econ)
    { E.Lam (xs, e) }

  | LET; pat = einvpat; sch = escheme; EQUALS; tm = located(econ); IN; body = located(econ)
    { E.Let {pat; sch = sch; tm; body} }

  | COE; r0 = located(atomic); r1 = located(atomic); tm = located(atomic); IN; fam = located(econ)
    { E.Coe {r = r0; r' = r1; fam; tm} }

  | tele = nonempty_list(etele_cell); RIGHT_ARROW; cod = located(econ)
    { E.Pi (List.flatten tele, cod) }

  | tele = nonempty_list(etele_cell); times_or_ast; cod = located(econ)
    { E.Sg (List.flatten tele, cod) }

  | dom = located(spine_con); RIGHT_ARROW; cod = located(econ)
    { E.Pi ([`Ty ("_", dom)], cod) }

  | dom = located(spine_con); times_or_ast; cod = located(econ)
    { E.Sg ([`Ty ("_", dom)], cod) }

eclause:
  | lbl = ATOM; pbinds = list(epatbind); RIGHT_ARROW; bdy = located(econ)
    { `Con (lbl, pbinds, bdy) }
  | AST RIGHT_ARROW; bdy = located(econ)
    { `All bdy }

epatbind:
  | x = einvpat
    { `Bind x }
  | LPR; x = einvpat; RIGHT_ARROW; ih = einvpat; RPR
    { `BindIH (x, ih) }

einvpat:
  | x = ATOM
    { `Var (`User x) }
  | AST
    { `Wildcard }
  | LPR; xs = separated_nonempty_list(COMMA, einvpat) RPR
    { let xs, x = ListUtil.split_last xs in
      List.fold_right (fun x xs -> `SplitAs (x, xs)) xs x }
  | LSQ; x = einvpat; COMMA; RSQ
    { `Bite x }
  | LSQ; COMMA; RSQ
    { `Split }

edimension:
  | n = NUMERAL;
    { E.Num n }
  | a = ATOM
    { atom_to_econ a }
  | LPR; d = edimension; RPR
    { d }

eequation:
  | r0 = located(edimension); EQUALS; r1 = located(edimension)
    { r0, r1 }

ecofib0:
  | xi = eequation
    { [xi] }

  | BOUNDARY; LSQ; xs = nonempty_list(ATOM); RSQ;
    { let xi x =
        let pos = $loc(xs) in
        let r = locate pos @@ E.Var {name = x; ushift = 0} in
        [r, locate pos (E.Num 0);
         r, locate pos (E.Num 1)]
      in
      List.flatten @@ List.map xi xs }

  | LPR; e = ecofib; RPR
    { e }

ecofib:
  | phi = separated_nonempty_list(PIPE, ecofib0)
    { List.flatten phi }

eface:
  | phi = ecofib; RIGHT_ARROW; e = located(econ)
    { phi, e }
  | phi = ecofib0; xs = nonempty_list(ATOM); RIGHT_ARROW; e = located(econ)
    { phi, locate ($startpos(xs), $endpos(e)) (E.Lam (List.map (fun x -> `Var (`User x)) xs, e)) }


escheme:
  | tele = list(etele_cell); COLON; cod = located(econ)
    { (List.flatten tele, cod) }

  | tele = list(etele_cell)
    { (List.flatten tele, locate ($endpos(tele), $endpos(tele)) E.Hope) }

etele_cell:
  | LPR; xs = nonempty_list(ATOM); COLON; ty = located(econ); RPR
    { List.map (fun x -> `Ty (x, ty)) xs }
  | LPR; xs = nonempty_list(ATOM); COLON; DIM; RPR
    { List.map (fun x -> `I x) xs }
  | DIM
    { [`I "_"] }


econstr:
| clbl = ATOM;
  specs = list(etele_cell)
  boundary = loption(pipe_block(eface))
  { clbl, E.EConstr {specs = List.flatten specs; boundary} }

data_modifiers:
  | PRIVATE
    { `Private }
  | { `Public }

def_modifiers:
  | OPAQUE
    { `Public, `Opaque }
  | PRIVATE
    { `Private, `Transparent }
  | OPAQUE PRIVATE
    { `Private, `Opaque }
  | PRIVATE OPAQUE
    { `Private, `Opaque }
  | { `Public, `Transparent }


data_decl:
  | DATA;
    params = edata_params;
    dlbl = ATOM;
    univ_spec = option(preceded(COLON, univ_spec));
    WHERE; option(PIPE);
    constrs = separated_list(PIPE, econstr);
    { let kind, lvl =
        match univ_spec with
        | Some (k, l) -> k, l
        | None -> `Kan, `Const 0
      in
      let params = List.flatten params in
      dlbl, E.EDesc {params; constrs; kind; lvl} }


mltoplevel:
  | META; LTR; LET; a = ATOM; EQUALS; cmd = mlcmd; RTR; rest = mltoplevel
    { {rest with con = E.MlBind (cmd, `User a, rest.con)} }

  | META; LTR; c = mlcmd; RTR; rest = mltoplevel
    { {rest with con = E.MlBind (c, `Gen (Name.fresh ()), rest.con)} }

  | modifiers = def_modifiers; DEF; a = ATOM; sch = escheme; EQUALS; tm = located(econ); rest = mltoplevel
    { let name = E.MlRef (Name.named (Some a)) in
      let visibility, opacity = modifiers in
      {rest with con = MlBind (E.define ~visibility ~name ~opacity ~scheme:sch ~tm, `User a, rest.con)} }

  | visibility = data_modifiers; decl = data_decl; rest = mltoplevel
    { let a, desc = decl in
      let name = E.MlRef (Name.named (Some a)) in
      {rest with con = MlBind (E.MlDeclData {visibility; name; desc}, `User a, rest.con)} }

  | path = IMPORT; rest = mltoplevel
    { {rest with con = E.mlbind (E.MlImport (`Private, path)) @@ fun _ -> rest.con} }

  | PUBLIC; path = IMPORT; rest = mltoplevel
    { {rest with con = E.mlbind (E.MlImport (`Public, path)) @@ fun _ -> rest.con} }

  | QUIT; rest = mltoplevel
    { {rest with con = E.MlRet (E.MlTuple [])} }

  | x = located(EOF)
    { {x with con = E.MlRet (E.MlTuple [])} }

  | error
    { raise @@ ParseError.E ($startpos, $endpos) }

mlcmd:
  | LET; a = ATOM; EQUALS; cmd = mlcmd; IN; rest = mlcmd
    { E.MlBind (cmd, `User a, rest) }

  | c = atomic_mlcmd; SEMI; rest = mlcmd
    { E.MlBind (c, `Gen (Name.fresh ()), rest) }

  | FUN; a = ATOM; RIGHT_ARROW; c = mlcmd
    { E.MlLam (`User a, c) }

  | CHECK; tm = mlval; COLON; ty = mlval
    { E.MlCheck {ty; tm} }

  | c = atomic_mlcmd; v = mlval
    { E.MlApp (c, v) }

  | c = atomic_mlcmd
    { c }

  | DEBUG; f = debug_filter
    { E.MlDebug f }


atomic_mlcmd:
  | LPR; c = mlcmd; RPR
    { c }
  | BEGIN; c = mlcmd; END
    { c }
  | BANG; v = mlval
    { E.MlUnleash v }

  | PRINT; c = located(atomic_mlcmd)
    { let open E in
      mlbind c.con @@ fun x ->
      MlPrint {c with con = x} }

  | NORMALIZE; c = atomic_mlcmd
    { E.mlbind c @@ fun x -> E.MlNormalize x }

  | LLGL; visibility = data_modifiers; decl = data_decl; RRGL
    { let name, desc = decl in
      let name = E.MlRef (Name.named (Some name)) in
      E.MlDeclData {visibility; name; desc} }

  | LLGL; modifiers = def_modifiers; DEF; a = ATOM; sch = escheme; EQUALS; tm = located(econ); RRGL
    { let name = E.MlRef (Name.named (Some a)) in
      let visibility, opacity = modifiers in
      E.define ~name ~visibility ~opacity ~scheme:sch ~tm }

  | LLGL; e = located(econ); RRGL
    { E.MlElab e }

  | v = mlval
    { E.MlRet v }


mlval:
  | LGL; vs = separated_list(COMMA, mlval); RGL
    { E.MlTuple vs }
  | LBR; c = mlcmd; RBR
    { E.MlThunk c }
  | s = STRING
    { E.MlString s }
  | a = ATOM;
    { E.MlVar (`User a) }




(*
edecl:
  | LET; a = ATOM; sch = escheme; EQUALS; tm = located(econ)
    { E.Define (a, `Transparent, sch, tm) }
  | OPAQUE LET; a = ATOM; sch = escheme; EQUALS; tm = located(econ)
    { E.Define (a, `Opaque, sch, tm) }
  | NORMALIZE; e = located(econ)
    { E.MlNormalize e }

(*

*)

  | IMPORT; a = ATOM
    { E.MlImport a }

    (*
  | QUIT
    { E.Quit }
    *)

    *)







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

  | LPR; times_or_ast; tele = tele; RPR
    { fun env ->
      sg_from_tele (Some ($startpos, $endpos)) @@ tele env }

  | LPR; HASH; mb = multibind(constrained); RPR
    { fun env ->
      ext_from_multibind $startpos $endpos @@ mb env }

  | LPR; LAM; mb = multibind(tm); RPR
    { fun env ->
      lam_from_multibind (Some ($startpos, $endpos)) @@ mb env }

  | LPR; PAIR; e0 = tm; e1 = tm; RPR
    { fun env ->
      make_node $startpos $endpos @@
      Tm.Cons (e0 env, e1 env) }

  | LPR; DATA; dlbl = ATOM; RPR
    { fun env ->
      make_node $startpos $endpos @@
      let alpha = R.get_name dlbl env in
      Tm.Data {lbl = alpha; params = []} }

  | LPR; dlbl = ATOM; DOT; INTRO; clbl = ATOM; es = elist(tm); RPR
    { fun env ->
      make_node $startpos $endpos @@
      let alpha = R.get_name dlbl env in
      Tm.Intro (alpha, clbl, [], es env) }

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
      | `Name x -> Tm.Var {name = x; twin = `Only; ushift = k} }

  | a = ATOM
    { fun env ->
      match R.get a env with
      | `Ix i -> Tm.Ix (i, `Only)
      | `Name x -> Tm.Var {name = x; twin = `Only; ushift = 0} }

  | LPR; HCOM; r0 = tm; r1 = tm; ty = tm; cap = tm; sys = elist(face(dimbind(tm))); RPR
    { fun env ->
      Tm.HCom {r = r0 env; r' = r1 env; ty = ty env; cap = cap env; sys = sys env} }

  | LPR; COM; r0 = tm; r1 = tm; ty = dimbind(tm); cap = tm; sys = elist(face(dimbind(tm))); RPR
    { fun env ->
      Tm.Com {r = r0 env; r' = r1 env; ty = ty env; cap = cap env; sys = sys env} }

  | LPR; COE; r0 = tm; r1 = tm; ty = dimbind(tm); tm = tm; RPR
    { fun env ->
      Tm.Coe {r = r0 env; r' = r1 env; ty = ty env; tm = tm env} }

  | LPR; COLON; ty = tm; tm = tm; RPR
    { fun env ->
      Tm.Down {ty = ty env; tm = tm env} }

cmd:
  | c = cut
    { fun env ->
      let hd, sp = c env in
      hd, Bwd.to_list sp }

cut:
  | hd = head
    { fun env ->
      hd env, Emp }

  | LPR; FST; e = cut; RPR
    { fun env ->
      let hd, fs = e env in
      hd, fs #< Tm.Fst }

  | LPR; SND; e = cut; RPR
    { fun env ->
      let hd, fs = e env in
      hd, fs #< Tm.Snd }

  | LPR; e = cut; arg0 = tm; rest = elist(tm); RPR
    { fun env ->
      let hd, fs = e env in
      let args = arg0 env :: rest env in
      hd, (fs <>< List.map (fun t -> Tm.FunApp t) args) }

  | LPR; AT; e = cut; args = elist(tm); RPR
    { fun env ->
      let hd, fs = e env in
      hd, fs #< (Tm.ExtApp (args env)) }

  | LPR; VPROJ; r = tm; e = cut; ty0 = tm; ty1 = tm; func = tm; RPR
    { fun env ->
      let hd, fs = e env in
      hd, fs #< (Tm.VProj {r = r env; ty0 = ty0 env; ty1 = ty1 env; func = func env})}
