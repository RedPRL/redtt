open RedBasis
open Bwd
open RedTT_Core
open Contextual

exception CanFavoniaHelpMe

module M = Monad.Notation (Contextual)
open M
module MU = Monad.Util (Contextual)

let read_rot_file _ = raise CanFavoniaHelpMe
let write_rot_file _ = raise CanFavoniaHelpMe

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
  | _ -> failwith "failed to parse an int"

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
  | _ -> failwith "unexpected kind!"

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

let yaml_of_name nm =
  `String (Option.default "" nm)

let name_of_yaml =
  function
  | `String "" -> None
  | `String str -> Some str
  | _ -> failwith "unexpected name!"

let yaml_of_name_bwd nms =
  `A (List.map yaml_of_name @@ Bwd.to_list nms)

let name_bwd_of_yaml =
  function
  | `A arr -> Bwd.from_list @@ List.map name_of_yaml arr
  | _ -> failwith "unexpected name!"

let rec yaml_of_tm tm =
  match Tm.unleash tm with
  | Tm.FHCom {r; r'; cap; sys} ->
    yaml_of_tm r >>= fun r ->
    yaml_of_tm r' >>= fun r' ->
    yaml_of_tm cap >>= fun cap ->
    yaml_of_bnd_sys sys >>= fun sys ->
    ret @@ `A [`String "fhcom"; r; r'; cap; sys]

  | Tm.Univ {kind; lvl} ->
    ret @@ `A [`String "univ"; yaml_of_kind kind; yaml_of_lvl lvl]

  | Tm.Pi (dom, B (nm, cod)) ->
    yaml_of_tm dom >>= fun dom ->
    yaml_of_tm cod >>= fun cod ->
    ret @@ `A [`String "pi"; dom; yaml_of_name nm; cod]

  | Tm.Ext (NB (nms, (tm, sys))) ->
    yaml_of_tm tm >>= fun tm ->
    yaml_of_tm_sys sys >>= fun sys ->
    ret @@ `A [`String "ext"; yaml_of_name_bwd nms; tm; sys]

  | Tm.Restrict face ->
    yaml_of_tm_face face >>= fun face ->
    ret @@ `A [`String "restrict"; face]

  | Tm.Sg (dom, B (nm, cod)) ->
    yaml_of_tm dom >>= fun dom ->
    yaml_of_tm cod >>= fun cod ->
    ret @@ `A [`String "sg"; dom; yaml_of_name nm; cod]

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
    ret @@ `A [`String "lam"; yaml_of_name nm; tm]
  
  | Tm.ExtLam (NB (nms, tm)) ->
    yaml_of_tm tm >>= fun tm ->
    ret @@ `A [`String "ext"; yaml_of_name_bwd nms; tm]
  
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
    ret @@ `A [`String "let"; cmd; yaml_of_name nm; tm]

  | Tm.Data _ -> raise CanFavoniaHelpMe
  
  | Tm.Intro _ -> raise CanFavoniaHelpMe

and yaml_of_meta ~name ~ushift =
  resolver >>= fun res ->
  match ResEnv.id_of_name_opt name res with
  | Some id -> ret @@ `A [`String "meta-self"; yaml_of_int id; yaml_of_int ushift]
  | None ->
    source_stem name >>= function
    | None -> expand_meta ~name ~ushift >>= yaml_of_tm
    | Some stem ->
      get_resolver stem >>= function
      | None ->
        Format.eprintf "Module at %s spreads variables without leaving a trace in the cache.@." stem;
        raise @@ Impossible "Impossible cache miss"
      | Some res ->
        match ResEnv.id_of_name_opt name res with
        | None -> expand_meta ~name ~ushift >>= yaml_of_tm
        | Some id -> ret @@ `A [`String "meta-other"; `String stem; yaml_of_int id; yaml_of_int ushift]

and yaml_of_var ~name ~twin ~ushift =
  resolver >>= fun res ->
  match ResEnv.id_of_name_opt name res with
  | Some id -> ret @@ `A [`String "var-self"; yaml_of_int id; yaml_of_twin twin; yaml_of_int ushift]
  | None ->
    source_stem name >>= function
    | None -> expand_var ~name ~twin ~ushift >>= yaml_of_tm
    | Some stem ->
      get_resolver stem >>= function
      | None ->
        Format.eprintf "Module at %s spreads variables without leaving a trace in the cache.@." stem;
        raise @@ Impossible "Impossible cache miss"
      | Some res ->
        match ResEnv.id_of_name_opt name res with
        | None -> expand_var ~name ~twin ~ushift >>= yaml_of_tm
        | Some id -> ret @@ `A [`String "var-other"; `String stem; yaml_of_int id; yaml_of_twin twin; yaml_of_int ushift]

and yaml_of_head =
  function
  | Tm.Meta {name; ushift} ->
    yaml_of_meta ~name ~ushift

  | Tm.Var {name; twin; ushift} ->
    yaml_of_var ~name ~twin ~ushift

  | Tm.Ix (ix, twin) ->
    ret @@ `A [`String "ix"; `String (string_of_int ix); yaml_of_twin twin]

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
    ret @@ `A [`String "coe"; r; r'; yaml_of_name nm; ty; tm]

  | Tm.HCom {r; r'; ty; cap; sys} ->
    yaml_of_tm r >>= fun r ->
    yaml_of_tm r' >>= fun r' ->
    yaml_of_tm ty >>= fun ty ->
    yaml_of_tm cap >>= fun cap ->
    yaml_of_bnd_sys sys >>= fun sys ->
    ret @@ `A [`String "hcom"; r; r'; ty; cap; sys]
  
  | Tm.Com {r; r'; ty = B (nm, ty); cap; sys} ->
    yaml_of_tm r >>= fun r ->
    yaml_of_tm r' >>= fun r' ->
    yaml_of_tm ty >>= fun ty ->
    yaml_of_tm cap >>= fun cap ->
    yaml_of_bnd_sys sys >>= fun sys ->
    ret @@ `A [`String "com"; r; r'; yaml_of_name nm; ty; cap; sys]
  
  | Tm.GHCom {r; r'; ty; cap; sys} ->
    yaml_of_tm r >>= fun r ->
    yaml_of_tm r' >>= fun r' ->
    yaml_of_tm ty >>= fun ty ->
    yaml_of_tm cap >>= fun cap ->
    yaml_of_bnd_sys sys >>= fun sys ->
    ret @@ `A [`String "ghcom"; r; r'; ty; cap; sys]
  
  | Tm.GCom {r; r'; ty = B (nm, ty); cap; sys} ->
    yaml_of_tm r >>= fun r ->
    yaml_of_tm r' >>= fun r' ->
    yaml_of_tm ty >>= fun ty ->
    yaml_of_tm cap >>= fun cap ->
    yaml_of_bnd_sys sys >>= fun sys ->
    ret @@ `A [`String "gcom"; r; r'; yaml_of_name nm; ty; cap; sys]

and yaml_of_frame : Tm.tm Tm.frame -> Yaml.value m =
  function
  | Tm.Fst -> ret @@ `String "fst"

  | Tm.Snd -> ret @@ `String "snd"

  | Tm.FunApp arg ->
    yaml_of_tm arg >>= fun arg ->
    ret @@ `A [`String "funapp"; arg]

  | Tm.ExtApp rs ->
    MU.traverse yaml_of_tm rs >>= fun rs ->
    ret @@ `A (`String "extapp" :: rs)

  | Tm.VProj {r; func} ->
    yaml_of_tm r >>= fun r ->
    yaml_of_tm func >>= fun func ->
    ret @@ `A [`String "vproj"; r; func]

  | Tm.Cap {r; r'; ty; sys} ->
    yaml_of_tm r >>= fun r ->
    yaml_of_tm r' >>= fun r' ->
    yaml_of_tm ty >>= fun ty ->
    yaml_of_bnd_sys sys >>= fun sys ->
    ret @@ `A [`String "cap"; r; r'; ty; sys]

  | Tm.RestrictForce -> ret @@ `String "restrictforce"

  | Tm.Elim _ -> raise CanFavoniaHelpMe

and yaml_of_cmd (hd, sp) =
  yaml_of_head hd >>= fun hd ->
  MU.traverse yaml_of_frame sp >>= fun sp ->
  ret @@ `A (hd :: sp)

and yaml_of_tm_face (r, r', otm) =
  yaml_of_tm r >>= fun r ->
  yaml_of_tm r' >>= fun r' ->
  match otm with
  | Some tm ->
    yaml_of_tm tm >>= fun tm ->
    ret @@ `A [r; r'; tm]
  | None ->
    ret @@ `A [r; r']

and yaml_of_tm_sys sys =
  MU.traverse yaml_of_tm_face sys <<@> fun x -> `A x

and yaml_of_bnd_face (r, r', obnd) =
  yaml_of_tm r >>= fun r ->
  yaml_of_tm r' >>= fun r' ->
  match obnd with
  | Some (Tm.B (nm, tm)) ->
    yaml_of_tm tm >>= fun tm ->
    ret @@ `A [r; r'; yaml_of_name nm; tm]
  | None ->
    ret @@ `A [r; r']

and yaml_of_bnd_sys sys =
  MU.traverse yaml_of_bnd_face sys <<@> fun x -> `A x
