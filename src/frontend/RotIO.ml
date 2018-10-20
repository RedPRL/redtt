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

let unsafe_mode = ref false
let set_unsafe_mode b = unsafe_mode := b

module BasicYaml =
struct

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

  let yaml_of_labeled_list yaml_of_a (l : (string * 'a) list) =
    MU.traverse (fun (lbl, a) -> yaml_of_a a <<@> fun a -> (lbl, a)) l <<@> fun l -> `O l

  let yaml_of_olabeled_list yaml_of_a (l : (string option * 'a) list) =
    MU.traverse (fun (lbl, a) -> yaml_of_a a <<@> fun a -> (Option.default "" lbl, a)) l <<@> fun l -> `O l
end

module TmYaml =
struct
  open BasicYaml
  open Tm

  let expand_meta ~name ~ushift =
    global_env >>= fun genv ->
    match GlobalEnv.lookup_with_twin genv name `Only with
    | _, None ->
      Format.eprintf "Meta variable %a is not expandable.@." Name.pp name;
      raise @@ Impossible "Some meta variable escapes the serialization context."
    | _, Some def ->
      ret @@ shift_univ ushift def

  let expand_var ~name ~ushift ~twin =
    global_env >>= fun genv ->
    match GlobalEnv.lookup_with_twin genv name twin with
    | _, None ->
      Format.eprintf "Variable %a is not expandable.@." Name.pp name;
      raise @@ Impossible "Some variable escapes the serialization context."
    | _, Some def ->
      ret @@ shift_univ ushift def

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

  let yaml_of_twin =
    function
    | `Only -> `String "only"
    | `TwinL -> `String "twinl"
    | `TwinR -> `String "twinr"

  let yaml_of_bnd yaml_of_bdy (B (nm, bdy)) =
    yaml_of_bdy bdy >>= fun bdy ->
    ret @@ `A [yaml_of_ostring nm; bdy]

  let yaml_of_nbnd yaml_of_bdy (NB (nms, bdy)) =
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
    match unleash tm with
    | FHCom {r; r'; cap; sys} ->
      yaml_of_tm r >>= fun r ->
      yaml_of_tm r' >>= fun r' ->
      yaml_of_tm cap >>= fun cap ->
      yaml_of_tm_bnd_sys sys >>= fun sys ->
      ret @@ `A [`String "fhcom"; r; r'; cap; sys]

    | Univ {kind; lvl} ->
      ret @@ `A [`String "univ"; yaml_of_kind kind; yaml_of_lvl lvl]

    | Pi (dom, cod) ->
      yaml_of_tm dom >>= fun dom ->
      yaml_of_bnd yaml_of_tm cod >>= fun cod ->
      ret @@ `A [`String "pi"; dom; cod]

    | Ext ext ->
      yaml_of_nbnd (yaml_of_pair (yaml_of_tm, yaml_of_tm_sys)) ext >>= fun ext ->
      ret @@ `A [`String "ext"; ext]

    | Restrict face ->
      yaml_of_tm_face face >>= fun face ->
      ret @@ `A [`String "restrict"; face]

    | Sg (dom, cod) ->
      yaml_of_tm dom >>= fun dom ->
      yaml_of_bnd yaml_of_tm cod >>= fun cod ->
      ret @@ `A [`String "sg"; dom; cod]

    | V {r; ty0; ty1; equiv} ->
      yaml_of_tm r >>= fun r ->
      yaml_of_tm ty0 >>= fun ty0 ->
      yaml_of_tm ty1 >>= fun ty1 ->
      yaml_of_tm equiv >>= fun equiv ->
      ret @@ `A [`String "v"; r; ty0; ty1; equiv]

    | VIn {r; tm0; tm1} ->
      yaml_of_tm r >>= fun r ->
      yaml_of_tm tm0 >>= fun tm0 ->
      yaml_of_tm tm1 >>= fun tm1 ->
      ret @@ `A [`String "vin"; r; tm0; tm1]

    | Lam (B (nm, tm)) ->
      yaml_of_tm tm >>= fun tm ->
      ret @@ `A [`String "lam"; yaml_of_ostring nm; tm]

    | ExtLam extlam ->
      yaml_of_nbnd yaml_of_tm extlam >>= fun extlam ->
      ret @@ `A [`String "extlam"; extlam]

    | RestrictThunk face ->
      yaml_of_tm_face face >>= fun face ->
      ret @@ `A [`String "restrictthunk"; face]

    | Cons (tm0, tm1) ->
      yaml_of_tm tm0 >>= fun tm0 ->
      yaml_of_tm tm1 >>= fun tm1 ->
      ret @@ `A [`String "cons"; tm0; tm1]

    | Dim0 -> ret @@ `String "dim0"

    | Dim1 -> ret @@ `String "dim1"

    | Box {r; r'; cap; sys} ->
      yaml_of_tm r >>= fun r ->
      yaml_of_tm r' >>= fun r' ->
      yaml_of_tm cap >>= fun cap ->
      yaml_of_tm_sys sys >>= fun sys ->
      ret @@ `A [`String "box"; r; r'; cap; sys]

    | Up cmd ->
      yaml_of_cmd cmd >>= fun cmd ->
      ret @@ `A [`String "up"; cmd]

    | Let (cmd, B (nm, tm)) ->
      yaml_of_cmd cmd >>= fun cmd ->
      yaml_of_tm tm >>= fun tm ->
      ret @@ `A [`String "let"; cmd; yaml_of_ostring nm; tm]

    | Data {lbl; params} ->
      yaml_of_dlbl lbl >>= fun lbl ->
      yaml_of_list yaml_of_tm params >>= fun params ->
      ret @@ `A [`String "data"; lbl; params]

    | Intro (dlbl, clbl, params, args) ->
      yaml_of_dlbl dlbl >>= fun dlbl ->
      yaml_of_list yaml_of_tm params >>= fun params ->
      yaml_of_list yaml_of_tm args >>= fun args ->
      ret @@ `A [`String "intro"; dlbl; yaml_of_string clbl; params; args]

  and yaml_of_head =
    function
    | Meta {name; ushift} ->
      yaml_of_meta ~name ~ushift

    | Var {name; twin; ushift} ->
      yaml_of_var ~name ~twin ~ushift

    | Ix (ix, twin) ->
      ret @@ `A [`String "ix"; yaml_of_int ix; yaml_of_twin twin]

    | Down {ty; tm} ->
      yaml_of_tm ty >>= fun ty ->
      yaml_of_tm tm >>= fun tm ->
      ret @@ `A [`String "down"; ty; tm]

    | DownX tm ->
      yaml_of_tm tm >>= fun tm ->
      ret @@ `A [`String "downx"; tm]

    | Coe {r; r'; ty = B (nm, ty); tm} ->
      yaml_of_tm r >>= fun r ->
      yaml_of_tm r' >>= fun r' ->
      yaml_of_tm ty >>= fun ty ->
      yaml_of_tm tm >>= fun tm ->
      ret @@ `A [`String "coe"; r; r'; yaml_of_ostring nm; ty; tm]

    | HCom {r; r'; ty; cap; sys} ->
      yaml_of_tm r >>= fun r ->
      yaml_of_tm r' >>= fun r' ->
      yaml_of_tm ty >>= fun ty ->
      yaml_of_tm cap >>= fun cap ->
      yaml_of_tm_bnd_sys sys >>= fun sys ->
      ret @@ `A [`String "hcom"; r; r'; ty; cap; sys]

    | Com {r; r'; ty = B (nm, ty); cap; sys} ->
      yaml_of_tm r >>= fun r ->
      yaml_of_tm r' >>= fun r' ->
      yaml_of_tm ty >>= fun ty ->
      yaml_of_tm cap >>= fun cap ->
      yaml_of_tm_bnd_sys sys >>= fun sys ->
      ret @@ `A [`String "com"; r; r'; yaml_of_ostring nm; ty; cap; sys]

    | GHCom {r; r'; ty; cap; sys} ->
      yaml_of_tm r >>= fun r ->
      yaml_of_tm r' >>= fun r' ->
      yaml_of_tm ty >>= fun ty ->
      yaml_of_tm cap >>= fun cap ->
      yaml_of_tm_bnd_sys sys >>= fun sys ->
      ret @@ `A [`String "ghcom"; r; r'; ty; cap; sys]

    | GCom {r; r'; ty = B (nm, ty); cap; sys} ->
      yaml_of_tm r >>= fun r ->
      yaml_of_tm r' >>= fun r' ->
      yaml_of_tm ty >>= fun ty ->
      yaml_of_tm cap >>= fun cap ->
      yaml_of_tm_bnd_sys sys >>= fun sys ->
      ret @@ `A [`String "gcom"; r; r'; yaml_of_ostring nm; ty; cap; sys]

  and yaml_of_frame =
    function
    | Fst -> ret @@ `String "fst"

    | Snd -> ret @@ `String "snd"

    | FunApp arg ->
      yaml_of_tm arg >>= fun arg ->
      ret @@ `A [`String "funapp"; arg]

    | ExtApp rs ->
      yaml_of_list yaml_of_tm rs >>= fun rs ->
      ret @@ `A [`String "extapp"; rs]

    | VProj {r; func} ->
      yaml_of_tm r >>= fun r ->
      yaml_of_tm func >>= fun func ->
      ret @@ `A [`String "vproj"; r; func]

    | Cap {r; r'; ty; sys} ->
      yaml_of_tm r >>= fun r ->
      yaml_of_tm r' >>= fun r' ->
      yaml_of_tm ty >>= fun ty ->
      yaml_of_tm_bnd_sys sys >>= fun sys ->
      ret @@ `A [`String "cap"; r; r'; ty; sys]

    | RestrictForce -> ret @@ `String "restrictforce"

    | Elim {dlbl; params; mot; clauses} ->
      yaml_of_dlbl dlbl >>= fun dlbl ->
      yaml_of_list yaml_of_tm params >>= fun params ->
      yaml_of_bnd yaml_of_tm mot >>= fun mot ->
      yaml_of_labeled_list (yaml_of_nbnd yaml_of_tm) clauses >>= fun clauses ->
      ret @@ `A [`String "elim"; dlbl; params; mot; clauses]

  and yaml_of_cmd cmd =
    yaml_of_pair (yaml_of_head, yaml_of_list yaml_of_frame) cmd

  and yaml_of_tm_face f = yaml_of_face yaml_of_tm yaml_of_tm f
  and yaml_of_tm_sys s = yaml_of_list yaml_of_tm_face s

  and yaml_of_tm_bnd_face f = yaml_of_face yaml_of_tm (yaml_of_bnd yaml_of_tm) f
  and yaml_of_tm_bnd_sys s = yaml_of_list yaml_of_tm_bnd_face s
end

module DescYaml =
struct
  open BasicYaml
  open TmYaml
  open Desc

  let yaml_of_rec_spec =
    function
    | Self -> ret @@ `String "self"

  let rec_spec_of_yaml =
    function
    | `String "self" -> ret Self
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
    | TNil e -> yaml_of_e e
    | TCons (a, tel) ->
      yaml_of_a a >>= fun a ->
      yaml_of_bnd (yaml_of_telescope yaml_of_a yaml_of_e) tel >>= fun tel ->
      ret @@ `A [a; tel]

  let yaml_of_constr =
    yaml_of_telescope yaml_of_arg_spec yaml_of_tm_sys

  let yaml_of_body =
    yaml_of_telescope yaml_of_tm (yaml_of_labeled_list yaml_of_constr)

  let yaml_of_desc =
    function
    | {kind; lvl; body; status = `Complete} ->
      yaml_of_body body >>= fun body ->
      ret @@ `A [yaml_of_kind kind; yaml_of_lvl lvl; body]
    | {status = `Partial; _} ->
      raise PartialDatatype
end

module RotYaml =
struct
  open BasicYaml
  open TmYaml
  open DescYaml
  open RotData

  let yaml_of_dep =
    function
    | True -> `String "true"
    | False -> `String "false"
    | SelfAt {stem} -> `A [`String "selfat"; yaml_of_string stem]
    | Redsum {hash} -> `A [`String "redsum"; yaml_of_string hash]
    | Libsum {hash} -> `A [`String "libsum"; yaml_of_string hash]
    | Rotsum {stem; hash} ->
      `A [`String "rotsum"; yaml_of_string stem; yaml_of_string hash]
    | Shell {cmd; exit} ->
      `A [`String "shell"]

  let yaml_of_ver = yaml_of_string

  let yaml_of_datum =
    function
    | Down {ty; tm} ->
      yaml_of_tm ty >>= fun ty ->
      yaml_of_tm tm >>= fun tm ->
      ret @@ `A [`String "down"; ty; tm]

    | Desc desc ->
      yaml_of_desc desc >>= fun desc ->
      ret @@ `A [`String "desc"; desc]

  let yaml_of_rot (Rot {ver; deps; res}) =
    yaml_of_olabeled_list yaml_of_datum res >>= fun res ->
    ret @@ `A [yaml_of_ver ver; `A (List.map yaml_of_dep deps); res]
end

let read_rot_file _ = raise CanFavoniaHelpMe
let write_rot_file _ = raise CanFavoniaHelpMe
