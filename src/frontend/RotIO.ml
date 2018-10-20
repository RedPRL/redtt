open RedBasis
open Bwd
open RedTT_Core
open Contextual

exception CanFavoniaHelpMe

module M = Monad.Notation (Contextual)
open M
module MU = Monad.Util (Contextual)

(* Tm *)

exception IllFormed
exception PartialDatatype
exception Impossible of string

let expand_meta ~name ~ushift =
  global_env >>= fun genv ->
  match GlobalEnv.lookup_with_twin genv name `Only with
  | _, None ->
    Format.eprintf "Meta variable %a is not expandable.@." Name.pp name;
    raise @@ Impossible "Some meta variable escapes the serialization context."
  | _, Some def ->
    ret @@ Tm.shift_univ ushift def

let expand_var ~name ~ushift ~twin =
  global_env >>= fun genv ->
  match GlobalEnv.lookup_with_twin genv name twin with
  | _, None ->
    Format.eprintf "Variable %a is not expandable.@." Name.pp name;
    raise @@ Impossible "Some variable escapes the serialization context."
  | _, Some def ->
    ret @@ Tm.shift_univ ushift def

let yaml_of_int i = `String (string_of_int i)

let int_of_yaml =
  function
  | `String s -> int_of_string s
  | _ -> raise IllFormed

let yaml_of_string s = `String s

let string_of_yaml =
  function
  | `String s -> s
  | _ -> raise IllFormed

let yaml_of_kind =
  function
  | `Reg -> `String "reg" (* wow! we have "regular" kinds? *)
  | `Kan -> `String "kan"
  | `Pre -> `String "pre"

let kind_of_yaml =
  function
  | "reg" -> `Reg
  | "kan" -> `Kan
  | "pre" -> `Pre
  | _ -> raise IllFormed

let yaml_of_lvl =
  function
  | `Omega -> `String "omega"
  | `Const i -> yaml_of_int i

let lvl_of_yaml =
  function
  | `String "omega" -> `Omega
  | s -> `Const (int_of_yaml s)

and yaml_of_twin =
  function
  | `Only -> `String "only"
  | `TwinL -> `String "twinl"
  | `TwinR -> `String "twinr"

let yaml_of_ostring =
  function
  | None -> `Null
  | Some str -> `String str

let ostring_of_yaml =
  function
  | `Null -> None
  | `String str -> Some str
  | _ -> raise IllFormed

let yaml_of_ostring_bwd nms =
  `A (List.map yaml_of_ostring @@ Bwd.to_list nms)

let ostring_bwd_of_yaml =
  function
  | `A arr -> Bwd.from_list @@ List.map ostring_of_yaml arr
  | _ -> raise IllFormed

let yaml_of_list yaml_of_item l =
  MU.traverse yaml_of_item l <<@> fun l -> `A l

let list_of_yaml item_of_yaml =
  function
  | `A l -> MU.traverse item_of_yaml l
  | _ -> raise IllFormed

let yaml_of_pair (yaml_of_a, yaml_of_b) (a, b) =
  yaml_of_a a >>= fun a ->
  yaml_of_b b >>= fun b ->
  ret @@ `A [a; b]

let pair_of_yaml (a_of_yaml, b_of_yaml) =
  function
  | `A [a, b] ->
    a_of_yaml a >>= fun a ->
    b_of_yaml b >>= fun b ->
    ret @@ (a, b)
  | _ -> raise IllFormed

let yaml_of_labeled yaml_of_label yaml_of_a (lbl, a) =
  yaml_of_a a <<@> fun a -> `A [yaml_of_label lbl; a]

let yaml_of_bnd yaml_of_bdy (Tm.B (nm, bdy)) =
  yaml_of_bdy bdy >>= fun bdy ->
  ret @@ `A [yaml_of_ostring nm; bdy]

let yaml_of_nbnd yaml_of_bdy (Tm.NB (nms, bdy)) =
  yaml_of_bdy bdy >>= fun bdy ->
  ret @@ `A [yaml_of_ostring_bwd nms; bdy]

let yaml_of_face yaml_of_r yaml_of_bdy (r, r', obdy) =
  yaml_of_r r >>= fun r ->
  yaml_of_r r' >>= fun r' ->
  match obdy with
  | Some bdy ->
    yaml_of_bdy bdy >>= fun bdy ->
    ret @@ `A [r; r'; bdy]
  | None ->
    ret @@ `A [r; r']

let rec yaml_of_name name kont_notfound kont_found =
  resolver >>= fun res ->
  match ResEnv.id_of_name_opt name res with
  | Some id -> kont_found @@ yaml_of_int id
  | None ->
    source_stem name >>= function
    | None -> kont_notfound ()
    | Some stem ->
      get_resolver stem >>= function
      | None ->
        Format.eprintf "Module at %s spread names around without leaving a trace in the cache.@." stem;
        raise @@ Impossible "impossible cache miss"
      | Some res ->
        match ResEnv.id_of_name_opt name res with
        | None -> kont_notfound ()
        | Some id -> kont_found @@ `A [`String stem; yaml_of_int id]

and yaml_of_meta ~name ~ushift =
  yaml_of_name name
    (fun () -> expand_meta ~name ~ushift >>= yaml_of_tm)
    (fun name -> ret @@ `A [`String "meta"; name; yaml_of_int ushift])

and yaml_of_var ~name ~twin ~ushift =
  yaml_of_name name
    (fun () -> expand_var ~name ~twin ~ushift >>= yaml_of_tm)
    (fun name -> ret @@ `A [`String "var"; name; yaml_of_twin twin; yaml_of_int ushift])

and yaml_of_dlbl dlbl =
  yaml_of_name dlbl (fun () -> raise @@ Impossible "datatype name escaped the serialization context.") ret

and yaml_of_tm tm =
  match Tm.unleash tm with
  | Tm.FHCom {r; r'; cap; sys} ->
    yaml_of_tm r >>= fun r ->
    yaml_of_tm r' >>= fun r' ->
    yaml_of_tm cap >>= fun cap ->
    yaml_of_tm_bnd_sys sys >>= fun sys ->
    ret @@ `A [`String "fhcom"; r; r'; cap; sys]

  | Tm.Univ {kind; lvl} ->
    ret @@ `A [`String "univ"; yaml_of_kind kind; yaml_of_lvl lvl]

  | Tm.Pi (dom, cod) ->
    yaml_of_tm dom >>= fun dom ->
    yaml_of_bnd yaml_of_tm cod >>= fun cod ->
    ret @@ `A [`String "pi"; dom; cod]

  | Tm.Ext ext ->
    yaml_of_nbnd (yaml_of_pair (yaml_of_tm, yaml_of_tm_sys)) ext >>= fun ext ->
    ret @@ `A [`String "ext"; ext]

  | Tm.Restrict face ->
    yaml_of_tm_face face >>= fun face ->
    ret @@ `A [`String "restrict"; face]

  | Tm.Sg (dom, cod) ->
    yaml_of_tm dom >>= fun dom ->
    yaml_of_bnd yaml_of_tm cod >>= fun cod ->
    ret @@ `A [`String "sg"; dom; cod]

  | Tm.V {r; ty0; ty1; equiv} ->
    yaml_of_tm r >>= fun r ->
    yaml_of_tm ty0 >>= fun ty0 ->
    yaml_of_tm ty1 >>= fun ty1 ->
    yaml_of_tm equiv >>= fun equiv ->
    ret @@ `A [`String "v"; r; ty0; ty1; equiv]
  
  | Tm.VIn {r; tm0; tm1} ->
    yaml_of_tm r >>= fun r ->
    yaml_of_tm tm0 >>= fun tm0 ->
    yaml_of_tm tm1 >>= fun tm1 ->
    ret @@ `A [`String "vin"; r; tm0; tm1]
  
  | Tm.Lam (B (nm, tm)) ->
    yaml_of_tm tm >>= fun tm ->
    ret @@ `A [`String "lam"; yaml_of_ostring nm; tm]
  
  | Tm.ExtLam extlam ->
    yaml_of_nbnd yaml_of_tm extlam >>= fun extlam ->
    ret @@ `A [`String "extlam"; extlam]
  
  | Tm.RestrictThunk face ->
    yaml_of_tm_face face >>= fun face ->
    ret @@ `A [`String "restrictthunk"; face]
  
  | Tm.Cons (tm0, tm1) ->
    yaml_of_tm tm0 >>= fun tm0 ->
    yaml_of_tm tm1 >>= fun tm1 ->
    ret @@ `A [`String "cons"; tm0; tm1]
  
  | Tm.Dim0 -> ret @@ `String "dim0"

  | Tm.Dim1 -> ret @@ `String "dim1"
  
  | Tm.Box {r; r'; cap; sys} ->
    yaml_of_tm r >>= fun r ->
    yaml_of_tm r' >>= fun r' ->
    yaml_of_tm cap >>= fun cap ->
    yaml_of_tm_sys sys >>= fun sys ->
    ret @@ `A [`String "box"; r; r'; cap; sys]

  | Tm.Up cmd ->
    yaml_of_cmd cmd >>= fun cmd ->
    ret @@ `A [`String "up"; cmd]
  
  | Tm.Let (cmd, B (nm, tm)) ->
    yaml_of_cmd cmd >>= fun cmd ->
    yaml_of_tm tm >>= fun tm ->
    ret @@ `A [`String "let"; cmd; yaml_of_ostring nm; tm]

  | Tm.Data {lbl; params} ->
    yaml_of_dlbl lbl >>= fun lbl ->
    yaml_of_list yaml_of_tm params >>= fun params ->
    ret @@ `A [`String "data"; lbl; params]
  
  | Tm.Intro (dlbl, clbl, params, args) ->
    yaml_of_dlbl dlbl >>= fun dlbl ->
    yaml_of_list yaml_of_tm params >>= fun params ->
    yaml_of_list yaml_of_tm args >>= fun args ->
    ret @@ `A [`String "intro"; dlbl; yaml_of_string clbl; params; args]

and yaml_of_head =
  function
  | Tm.Meta {name; ushift} ->
    yaml_of_meta ~name ~ushift

  | Tm.Var {name; twin; ushift} ->
    yaml_of_var ~name ~twin ~ushift

  | Tm.Ix (ix, twin) ->
    ret @@ `A [`String "ix"; yaml_of_int ix; yaml_of_twin twin]

  | Tm.Down {ty; tm} ->
    yaml_of_tm ty >>= fun ty ->
    yaml_of_tm tm >>= fun tm ->
    ret @@ `A [`String "down"; ty; tm]

  | Tm.DownX tm ->
    yaml_of_tm tm >>= fun tm ->
    ret @@ `A [`String "downx"; tm]
  
  | Tm.Coe {r; r'; ty = B (nm, ty); tm} ->
    yaml_of_tm r >>= fun r ->
    yaml_of_tm r' >>= fun r' ->
    yaml_of_tm ty >>= fun ty ->
    yaml_of_tm tm >>= fun tm ->
    ret @@ `A [`String "coe"; r; r'; yaml_of_ostring nm; ty; tm]

  | Tm.HCom {r; r'; ty; cap; sys} ->
    yaml_of_tm r >>= fun r ->
    yaml_of_tm r' >>= fun r' ->
    yaml_of_tm ty >>= fun ty ->
    yaml_of_tm cap >>= fun cap ->
    yaml_of_tm_bnd_sys sys >>= fun sys ->
    ret @@ `A [`String "hcom"; r; r'; ty; cap; sys]
  
  | Tm.Com {r; r'; ty = B (nm, ty); cap; sys} ->
    yaml_of_tm r >>= fun r ->
    yaml_of_tm r' >>= fun r' ->
    yaml_of_tm ty >>= fun ty ->
    yaml_of_tm cap >>= fun cap ->
    yaml_of_tm_bnd_sys sys >>= fun sys ->
    ret @@ `A [`String "com"; r; r'; yaml_of_ostring nm; ty; cap; sys]
  
  | Tm.GHCom {r; r'; ty; cap; sys} ->
    yaml_of_tm r >>= fun r ->
    yaml_of_tm r' >>= fun r' ->
    yaml_of_tm ty >>= fun ty ->
    yaml_of_tm cap >>= fun cap ->
    yaml_of_tm_bnd_sys sys >>= fun sys ->
    ret @@ `A [`String "ghcom"; r; r'; ty; cap; sys]
  
  | Tm.GCom {r; r'; ty = B (nm, ty); cap; sys} ->
    yaml_of_tm r >>= fun r ->
    yaml_of_tm r' >>= fun r' ->
    yaml_of_tm ty >>= fun ty ->
    yaml_of_tm cap >>= fun cap ->
    yaml_of_tm_bnd_sys sys >>= fun sys ->
    ret @@ `A [`String "gcom"; r; r'; yaml_of_ostring nm; ty; cap; sys]

and yaml_of_frame =
  function
  | Tm.Fst -> ret @@ `String "fst"

  | Tm.Snd -> ret @@ `String "snd"

  | Tm.FunApp arg ->
    yaml_of_tm arg >>= fun arg ->
    ret @@ `A [`String "funapp"; arg]

  | Tm.ExtApp rs ->
    yaml_of_list yaml_of_tm rs >>= fun rs ->
    ret @@ `A [`String "extapp"; rs]

  | Tm.VProj {r; func} ->
    yaml_of_tm r >>= fun r ->
    yaml_of_tm func >>= fun func ->
    ret @@ `A [`String "vproj"; r; func]

  | Tm.Cap {r; r'; ty; sys} ->
    yaml_of_tm r >>= fun r ->
    yaml_of_tm r' >>= fun r' ->
    yaml_of_tm ty >>= fun ty ->
    yaml_of_tm_bnd_sys sys >>= fun sys ->
    ret @@ `A [`String "cap"; r; r'; ty; sys]

  | Tm.RestrictForce -> ret @@ `String "restrictforce"

  | Tm.Elim {dlbl; params; mot; clauses} ->
    let yaml_of_clause = yaml_of_labeled yaml_of_string @@ yaml_of_nbnd yaml_of_tm in
    yaml_of_dlbl dlbl >>= fun dlbl ->
    yaml_of_list yaml_of_tm params >>= fun params ->
    yaml_of_bnd yaml_of_tm mot >>= fun mot ->
    yaml_of_list yaml_of_clause clauses >>= fun clauses ->
    ret @@ `A [`String "elim"; dlbl; params; mot; clauses]

and yaml_of_cmd cmd =
  yaml_of_pair (yaml_of_head, yaml_of_list yaml_of_frame) cmd

and yaml_of_tm_face f = yaml_of_face yaml_of_tm yaml_of_tm f
and yaml_of_tm_sys s = yaml_of_list yaml_of_tm_face s

and yaml_of_tm_bnd_face f = yaml_of_face yaml_of_tm (yaml_of_bnd yaml_of_tm) f
and yaml_of_tm_bnd_sys s = yaml_of_list yaml_of_tm_bnd_face s

(* Desc *)

let yaml_of_rec_spec =
  function
  | Desc.Self -> ret @@ `String "self"

let rec_spec_of_yaml =
  function
  | `String "self" -> ret Desc.Self
  | _ -> raise IllFormed

let yaml_of_arg_spec =
  function
  | `Const tm ->
    yaml_of_tm tm >>= fun tm ->
    ret @@ `A [`String "const"; tm]

  | `Rec rec_spec ->
    yaml_of_rec_spec rec_spec >>= fun rec_spec ->
    ret @@ `A [`String "rec"; rec_spec]

  | `Dim -> ret @@ `String "dim"

(* MORTALITY there's a better encoding *)
let rec yaml_of_telescope yaml_of_a yaml_of_e =
  function
  | Desc.TNil e -> yaml_of_e e
  | Desc.TCons (a, tel) ->
    yaml_of_a a >>= fun a ->
    yaml_of_bnd (yaml_of_telescope yaml_of_a yaml_of_e) tel >>= fun tel ->
    ret @@ `A [a; tel]

let yaml_of_constr : Desc.constr -> Yaml.value m =
  yaml_of_telescope yaml_of_arg_spec yaml_of_tm_sys

let yaml_of_constrs : Desc.constrs -> Yaml.value m =
  yaml_of_list @@ yaml_of_labeled yaml_of_string yaml_of_constr

let yaml_of_body : Desc.body -> Yaml.value m =
  yaml_of_telescope yaml_of_tm yaml_of_constrs

let yaml_of_desc : Desc.desc -> Yaml.value m =
  function
  | {kind; lvl; body; status = `Complete} ->
    yaml_of_body body >>= fun body ->
    ret @@ `A [yaml_of_kind kind; yaml_of_lvl lvl; body]
  | {status = `Partial; _} ->
    raise PartialDatatype

let read_rot_file _ = raise CanFavoniaHelpMe
let write_rot_file _ = raise CanFavoniaHelpMe
