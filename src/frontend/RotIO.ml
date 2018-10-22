open RedBasis
open Bwd
open RedTT_Core
open NewContextual

module M = Monad.Notation (NewContextual)
open M
module MU = Monad.Util (NewContextual)

(* Tm *)

exception IllFormed
exception PartialDatatype
exception Impossible of string

let unsafe_mode = ref false
let set_unsafe_mode b = unsafe_mode := b

module BasicJson =
struct

  let json_of_int i = `String (string_of_int i)

  let int_of_json =
    function
    | `String s -> int_of_string s
    | _ -> raise IllFormed

  let json_of_string s = `String s

  let string_of_json =
    function
    | `String s -> s
    | _ -> raise IllFormed

  let json_of_ostring =
    function
    | None -> `Null
    | Some str -> `String str

  let ostring_of_json =
    function
    | `Null -> None
    | `String str -> Some str
    | _ -> raise IllFormed

  let json_of_ostring_bwd nms =
    `A (List.map json_of_ostring @@ Bwd.to_list nms)

  let ostring_bwd_of_json =
    function
    | `A arr -> Bwd.from_list @@ List.map ostring_of_json arr
    | _ -> raise IllFormed

  let json_of_list json_of_item l =
    MU.traverse json_of_item l <<@> fun l -> `A l

  let list_of_json item_of_json =
    function
    | `A l -> MU.traverse item_of_json l
    | _ -> raise IllFormed

  let json_of_pair (json_of_a, json_of_b) (a, b) =
    json_of_a a >>= fun a ->
    json_of_b b >>= fun b ->
    ret @@ `A [a; b]

  let pair_of_json (a_of_json, b_of_json) =
    function
    | `A [a; b] ->
      a_of_json a >>= fun a ->
      b_of_json b >>= fun b ->
      ret @@ (a, b)
    | _ -> raise IllFormed

  let json_of_labeled_list json_of_a (l : (string * 'a) list) =
    MU.traverse (fun (lbl, a) -> json_of_a a <<@> fun a -> (lbl, a)) l <<@> fun l -> `O l

  let json_of_olabeled_list json_of_a (l : (string option * 'a) list) =
    MU.traverse (fun (lbl, a) -> json_of_a a <<@> fun a -> (Option.default "" lbl, a)) l <<@> fun l -> `O l
end

module TmJson =
struct
  open BasicJson
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

  let json_of_kind =
    function
    | `Reg -> `String "Reg" (* wow! we have "regular" kinds? *)
    | `Kan -> `String "Kan"
    | `Pre -> `String "Pre"

  let kind_of_json =
    function
    | `String "Reg" -> `Reg
    | `String "Kan" -> `Kan
    | `String "Pre" -> `Pre
    | _ -> raise IllFormed

  let json_of_lvl =
    function
    | `Omega -> `String "Omega"
    | `Const i -> json_of_int i

  let lvl_of_json =
    function
    | `String "Omega" -> `Omega
    | s -> `Const (int_of_json s)

  let json_of_twin =
    function
    | `Only -> `String "Only"
    | `TwinL -> `String "TwinL"
    | `TwinR -> `String "TwinR"

  let twin_of_json =
    function
    | `String "Only" -> `Only
    | `String "TwinL" -> `TwinL
    | `String "TwinR" -> `TwinR
    | _ -> raise IllFormed

  let json_of_bnd json_of_bdy (B (nm, bdy)) =
    json_of_bdy bdy >>= fun bdy ->
    ret @@ `A [json_of_ostring nm; bdy]

  let bnd_of_json bdy_of_json =
    function
    | `A [nm; bdy] ->
      bdy_of_json bdy >>= fun bdy ->
      ret @@ (B (ostring_of_json nm, bdy))
    | _ -> raise IllFormed

  let json_of_nbnd json_of_bdy (NB (nms, bdy)) =
    json_of_bdy bdy >>= fun bdy ->
    ret @@ `A [json_of_ostring_bwd nms; bdy]

  let nbnd_of_json bdy_of_json =
    function
    | `A [nms; bdy] ->
      bdy_of_json bdy >>= fun bdy ->
      ret @@ (NB (ostring_bwd_of_json nms, bdy))
    | _ -> raise IllFormed

  let json_of_face json_of_r json_of_bdy (r, r', obdy) =
    json_of_r r >>= fun r ->
    json_of_r r' >>= fun r' ->
    match obdy with
    | Some bdy ->
      json_of_bdy bdy >>= fun bdy ->
      ret @@ `A [r; r'; bdy]
    | None ->
      ret @@ `A [r; r']

  let rec json_of_name name kont_notfound kont_found =
    resolver >>= fun res ->
    match ResEnv.native_of_name name res with
    | Some native -> kont_found @@ json_of_int native
    | None ->
      source_stem name >>= function
      | None -> kont_notfound ()
      | Some stem ->
        cached_resolver stem >>= function
        | None ->
          Format.eprintf "Module at %s spread names around without leaving a trace in the cache.@." stem;
          raise @@ Impossible "impossible cache miss"
        | Some (res, _) ->
          match ResEnv.native_of_name name res with
          | None -> kont_notfound ()
          | Some native -> kont_found @@ `A [`String stem; json_of_int native]

  and json_of_dlbl dlbl =
    json_of_name dlbl (fun () -> raise @@ Impossible "datatype name escaped the serialization context.") ret

  and json_of_tm tm =
    match unleash tm with
    | FHCom {r; r'; cap; sys} ->
      json_of_tm r >>= fun r ->
      json_of_tm r' >>= fun r' ->
      json_of_tm cap >>= fun cap ->
      json_of_tm_bnd_sys sys >>= fun sys ->
      ret @@ `A [`String "FHCom"; r; r'; cap; sys]

    | Univ {kind; lvl} ->
      ret @@ `A [`String "Univ"; json_of_kind kind; json_of_lvl lvl]

    | Pi (dom, cod) ->
      json_of_tm dom >>= fun dom ->
      json_of_bnd json_of_tm cod >>= fun cod ->
      ret @@ `A [`String "Pi"; dom; cod]

    | Ext ext ->
      json_of_nbnd (json_of_pair (json_of_tm, json_of_tm_sys)) ext >>= fun ext ->
      ret @@ `A [`String "Ext"; ext]

    | Restrict face ->
      json_of_tm_face face >>= fun face ->
      ret @@ `A [`String "restrict"; face]

    | Sg (dom, cod) ->
      json_of_tm dom >>= fun dom ->
      json_of_bnd json_of_tm cod >>= fun cod ->
      ret @@ `A [`String "Sg"; dom; cod]

    | V {r; ty0; ty1; equiv} ->
      json_of_tm r >>= fun r ->
      json_of_tm ty0 >>= fun ty0 ->
      json_of_tm ty1 >>= fun ty1 ->
      json_of_tm equiv >>= fun equiv ->
      ret @@ `A [`String "V"; r; ty0; ty1; equiv]

    | VIn {r; tm0; tm1} ->
      json_of_tm r >>= fun r ->
      json_of_tm tm0 >>= fun tm0 ->
      json_of_tm tm1 >>= fun tm1 ->
      ret @@ `A [`String "VIn"; r; tm0; tm1]

    | Lam lam ->
      json_of_bnd json_of_tm lam >>= fun lam ->
      ret @@ `A [`String "Lam"; lam]

    | ExtLam extlam ->
      json_of_nbnd json_of_tm extlam >>= fun extlam ->
      ret @@ `A [`String "ExtLam"; extlam]

    | RestrictThunk face ->
      json_of_tm_face face >>= fun face ->
      ret @@ `A [`String "RestrictThunk"; face]

    | Cons (tm0, tm1) ->
      json_of_tm tm0 >>= fun tm0 ->
      json_of_tm tm1 >>= fun tm1 ->
      ret @@ `A [`String "Cons"; tm0; tm1]

    | Dim0 -> ret @@ `String "Dim0"

    | Dim1 -> ret @@ `String "Dim1"

    | Box {r; r'; cap; sys} ->
      json_of_tm r >>= fun r ->
      json_of_tm r' >>= fun r' ->
      json_of_tm cap >>= fun cap ->
      json_of_tm_sys sys >>= fun sys ->
      ret @@ `A [`String "Box"; r; r'; cap; sys]

    | Up cmd ->
      json_of_cmd cmd >>= fun cmd ->
      ret @@ `A [`String "Up"; cmd]

    | Let (cmd, bnd) ->
      json_of_cmd cmd >>= fun cmd ->
      json_of_bnd json_of_tm bnd >>= fun bnd ->
      ret @@ `A [`String "Let"; cmd; bnd]

    | Data {lbl; params} ->
      json_of_dlbl lbl >>= fun lbl ->
      json_of_list json_of_tm params >>= fun params ->
      ret @@ `A [`String "Data"; lbl; params]

    | Intro (dlbl, clbl, params, args) ->
      json_of_dlbl dlbl >>= fun dlbl ->
      json_of_list json_of_tm params >>= fun params ->
      json_of_list json_of_tm args >>= fun args ->
      ret @@ `A [`String "Intro"; dlbl; json_of_string clbl; params; args]

  and json_of_head =
    function
    | Meta {name; ushift} ->
      json_of_name name
        (fun () -> expand_meta ~name ~ushift >>= json_of_tm)
        (fun name -> ret @@ `A [`String "Meta"; name; json_of_int ushift])

    | Var {name; twin; ushift} ->
      json_of_name name
        (fun () -> expand_var ~name ~twin ~ushift >>= json_of_tm)
        (fun name -> ret @@ `A [`String "Var"; name; json_of_twin twin; json_of_int ushift])

    | Ix (ix, twin) ->
      ret @@ `A [`String "Ix"; json_of_int ix; json_of_twin twin]

    | Down {ty; tm} ->
      json_of_tm ty >>= fun ty ->
      json_of_tm tm >>= fun tm ->
      ret @@ `A [`String "Down"; ty; tm]

    | DownX tm ->
      json_of_tm tm >>= fun tm ->
      ret @@ `A [`String "DownX"; tm]

    | Coe {r; r'; ty; tm} ->
      json_of_tm r >>= fun r ->
      json_of_tm r' >>= fun r' ->
      json_of_bnd json_of_tm ty >>= fun ty ->
      json_of_tm tm >>= fun tm ->
      ret @@ `A [`String "Coe"; r; r'; ty; tm]

    | HCom {r; r'; ty; cap; sys} ->
      json_of_tm r >>= fun r ->
      json_of_tm r' >>= fun r' ->
      json_of_tm ty >>= fun ty ->
      json_of_tm cap >>= fun cap ->
      json_of_tm_bnd_sys sys >>= fun sys ->
      ret @@ `A [`String "HCom"; r; r'; ty; cap; sys]

    | Com {r; r'; ty; cap; sys} ->
      json_of_tm r >>= fun r ->
      json_of_tm r' >>= fun r' ->
      json_of_bnd json_of_tm ty >>= fun ty ->
      json_of_tm cap >>= fun cap ->
      json_of_tm_bnd_sys sys >>= fun sys ->
      ret @@ `A [`String "Com"; r; r'; ty; cap; sys]

    | GHCom {r; r'; ty; cap; sys} ->
      json_of_tm r >>= fun r ->
      json_of_tm r' >>= fun r' ->
      json_of_tm ty >>= fun ty ->
      json_of_tm cap >>= fun cap ->
      json_of_tm_bnd_sys sys >>= fun sys ->
      ret @@ `A [`String "GHCom"; r; r'; ty; cap; sys]

    | GCom {r; r'; ty; cap; sys} ->
      json_of_tm r >>= fun r ->
      json_of_tm r' >>= fun r' ->
      json_of_bnd json_of_tm ty >>= fun ty ->
      json_of_tm cap >>= fun cap ->
      json_of_tm_bnd_sys sys >>= fun sys ->
      ret @@ `A [`String "GCom"; r; r'; ty; cap; sys]

  and json_of_frame =
    function
    | Fst -> ret @@ `String "Fst"

    | Snd -> ret @@ `String "Snd"

    | FunApp arg ->
      json_of_tm arg >>= fun arg ->
      ret @@ `A [`String "FunApp"; arg]

    | ExtApp rs ->
      json_of_list json_of_tm rs >>= fun rs ->
      ret @@ `A [`String "ExtApp"; rs]

    | VProj {r; func} ->
      json_of_tm r >>= fun r ->
      json_of_tm func >>= fun func ->
      ret @@ `A [`String "VProj"; r; func]

    | Cap {r; r'; ty; sys} ->
      json_of_tm r >>= fun r ->
      json_of_tm r' >>= fun r' ->
      json_of_tm ty >>= fun ty ->
      json_of_tm_bnd_sys sys >>= fun sys ->
      ret @@ `A [`String "Cap"; r; r'; ty; sys]

    | RestrictForce -> ret @@ `String "RestrictForce"

    | Elim {dlbl; params; mot; clauses} ->
      json_of_dlbl dlbl >>= fun dlbl ->
      json_of_list json_of_tm params >>= fun params ->
      json_of_bnd json_of_tm mot >>= fun mot ->
      json_of_labeled_list (json_of_nbnd json_of_tm) clauses >>= fun clauses ->
      ret @@ `A [`String "Elim"; dlbl; params; mot; clauses]

  and json_of_cmd cmd =
    json_of_pair (json_of_head, json_of_list json_of_frame) cmd

  and json_of_tm_face face = json_of_face json_of_tm json_of_tm face
  and json_of_tm_sys sys = json_of_list json_of_tm_face sys

  and json_of_tm_bnd_face face = json_of_face json_of_tm (json_of_bnd json_of_tm) face
  and json_of_tm_bnd_sys sys = json_of_list json_of_tm_bnd_face sys



  exception PleaseFillIn

  let rec name_of_json : Ezjsonm.value -> Name.t m =
    function
    | `String native ->
      resolver >>= fun res ->
      begin match ResEnv.name_of_native (int_of_json (`String native)) res with
        | None -> raise IllFormed
        | Some name -> ret name
      end
    | `A [`String stem; native] ->
      cached_resolver stem >>= begin function
        | None -> raise IllFormed
        | Some (res, _) ->
          match ResEnv.name_of_native (int_of_json native) res with
          | None -> raise IllFormed
          | Some name -> ret name
      end
    | _ -> raise IllFormed

  and dlbl_of_json json = name_of_json json

  and tm_of_json (json : Ezjsonm.value) : tm m =
    make <@>> tm_of_json_ json

  and tm_of_json_ =
    function
    | `A [`String "FHCom"; r; r'; cap; sys] ->
      tm_of_json r >>= fun r ->
      tm_of_json r' >>= fun r' ->
      tm_of_json cap >>= fun cap ->
      tm_bnd_sys_of_json sys >>= fun sys ->
      ret @@ FHCom {r; r'; cap; sys}

    | `A [`String "Univ"; kind; lvl] ->
      ret @@ Univ {kind = kind_of_json kind; lvl = lvl_of_json lvl}

    | `A [`String "Pi"; dom; cod] ->
      tm_of_json dom >>= fun dom ->
      bnd_of_json tm_of_json cod >>= fun cod ->
      ret @@ Pi (dom, cod)

    | `A [`String "Ext"; ext] ->
      nbnd_of_json (pair_of_json (tm_of_json, tm_sys_of_json)) ext >>= fun ext ->
      ret @@ Ext ext

    | `A [`String "Restrict"; face] ->
      tm_face_of_json face >>= fun face ->
      ret @@ Restrict face

    | `A [`String "Sg"; dom; cod] ->
      tm_of_json dom >>= fun dom ->
      bnd_of_json tm_of_json cod >>= fun cod ->
      ret @@ Sg (dom, cod)

    | `A [`String "V"; r; ty0; ty1; equiv] ->
      tm_of_json r >>= fun r ->
      tm_of_json ty0 >>= fun ty0 ->
      tm_of_json ty1 >>= fun ty1 ->
      tm_of_json equiv >>= fun equiv ->
      ret @@ V {r; ty0; ty1; equiv}

    | `A [`String "VIn"; r; tm0; tm1] ->
      tm_of_json r >>= fun r ->
      tm_of_json tm0 >>= fun tm0 ->
      tm_of_json tm1 >>= fun tm1 ->
      ret @@ VIn {r; tm0; tm1}

    | `A [`String "Lam"; lam] ->
      bnd_of_json tm_of_json lam >>= fun lam ->
      ret @@ Lam lam

    | `A [`String "ExtLam"; extlam] ->
      nbnd_of_json tm_of_json extlam >>= fun extlam ->
      ret @@ ExtLam extlam

    | `A [`String "RestrictThunk"; face] ->
      tm_face_of_json face >>= fun face ->
      ret @@ RestrictThunk face

    | `A [`String "Cons"; tm0; tm1] ->
      tm_of_json tm0 >>= fun tm0 ->
      tm_of_json tm1 >>= fun tm1 ->
      ret @@ Cons (tm0, tm1)

    | `String "Dim0" -> ret Dim0

    | `String "Dim1" -> ret Dim1

    | `A [`String "Box"; r; r'; cap; sys] ->
      tm_of_json r >>= fun r ->
      tm_of_json r' >>= fun r' ->
      tm_of_json cap >>= fun cap ->
      tm_sys_of_json sys >>= fun sys ->
      ret @@ Box {r; r'; cap; sys}

    | `A [`String "Up"; cmd] ->
      cmd_of_json cmd >>= fun cmd ->
      ret @@ Up cmd

    | `A [`String "Let"; cmd; bnd] ->
      cmd_of_json cmd >>= fun cmd ->
      bnd_of_json tm_of_json bnd >>= fun bnd ->
      ret @@ Let (cmd, bnd)

    | `A [`String "Data"; lbl; params] ->
      dlbl_of_json lbl >>= fun lbl ->
      list_of_json tm_of_json params >>= fun params ->
      ret @@ Data {lbl; params}

    | `A [`String "Intro"; dlbl; clbl; params; args] ->
      dlbl_of_json dlbl >>= fun dlbl ->
      list_of_json tm_of_json params >>= fun params ->
      list_of_json tm_of_json args >>= fun args ->
      ret @@ Intro (dlbl, string_of_json clbl, params, args)

    | _ -> raise IllFormed

  and json_of_head : Ezjsonm.value -> tm head m =
    function
    | `A [`String "Meta"; name; ushift] ->
      name_of_json name >>= fun name ->
      ret @@ Meta {name; ushift = int_of_json ushift}

    | `A [`String "Var"; name; twin; ushift] ->
      name_of_json name >>= fun name ->
      ret @@ Var {name; twin = twin_of_json twin; ushift = int_of_json ushift}

    | `A [`String "Ix"; ix; twin] ->
      ret @@ Ix (int_of_json ix, twin_of_json twin)

    | `A [`String "Down"; ty; tm] ->
      tm_of_json ty >>= fun ty ->
      tm_of_json tm >>= fun tm ->
      ret @@ Down {ty; tm}

    | `A [`String "DownX"; tm] ->
      tm_of_json tm >>= fun tm ->
      ret @@ DownX tm

    | `A [`String "Coe"; r; r'; ty; tm] ->
      tm_of_json r >>= fun r ->
      tm_of_json r' >>= fun r' ->
      bnd_of_json tm_of_json ty >>= fun ty ->
      tm_of_json tm >>= fun tm ->
      ret @@ Coe {r; r'; ty; tm}

    | `A [`String "HCom"; r; r'; ty; cap; sys] ->
      tm_of_json r >>= fun r ->
      tm_of_json r' >>= fun r' ->
      tm_of_json ty >>= fun ty ->
      tm_of_json cap >>= fun cap ->
      tm_bnd_sys_of_json sys >>= fun sys ->
      ret @@ HCom {r; r'; ty; cap; sys}

    | `A [`String "Com"; r; r'; ty; cap; sys] ->
      tm_of_json r >>= fun r ->
      tm_of_json r' >>= fun r' ->
      bnd_of_json tm_of_json ty >>= fun ty ->
      tm_of_json cap >>= fun cap ->
      tm_bnd_sys_of_json sys >>= fun sys ->
      ret @@ Com {r; r'; ty; cap; sys}

    | `A [`String "GHCom"; r; r'; ty; cap; sys] ->
      tm_of_json r >>= fun r ->
      tm_of_json r' >>= fun r' ->
      tm_of_json ty >>= fun ty ->
      tm_of_json cap >>= fun cap ->
      tm_bnd_sys_of_json sys >>= fun sys ->
      ret @@ GHCom {r; r'; ty; cap; sys}

    | `A [`String "GCom"; r; r'; ty; cap; sys] ->
      tm_of_json r >>= fun r ->
      tm_of_json r' >>= fun r' ->
      bnd_of_json tm_of_json ty >>= fun ty ->
      tm_of_json cap >>= fun cap ->
      tm_bnd_sys_of_json sys >>= fun sys ->
      ret @@ GCom {r; r'; ty; cap; sys}

    | _ -> raise IllFormed

  and cmd_of_json sys = raise PleaseFillIn
  and tm_face_of_json sys = raise PleaseFillIn
  and tm_sys_of_json sys = raise PleaseFillIn
  and tm_bnd_sys_of_json sys = raise PleaseFillIn

end

module DescJson =
struct
  open BasicJson
  open TmJson
  open Desc

  let json_of_rec_spec =
    function
    | Self -> ret @@ `String "self"

  let rec_spec_of_json =
    function
    | `String "self" -> ret Self
    | _ -> raise IllFormed

  let json_of_arg_spec =
    function
    | `Const tm ->
      json_of_tm tm >>= fun tm ->
      ret @@ `A [`String "const"; tm]

    | `Rec rec_spec ->
      json_of_rec_spec rec_spec >>= fun rec_spec ->
      ret @@ `A [`String "rec"; rec_spec]

    | `Dim -> ret @@ `String "dim"

  (* MORTALITY there's a better encoding *)
  let rec json_of_telescope json_of_a json_of_e =
    function
    | TNil e -> json_of_e e
    | TCons (a, tel) ->
      json_of_a a >>= fun a ->
      json_of_bnd (json_of_telescope json_of_a json_of_e) tel >>= fun tel ->
      ret @@ `A [a; tel]

  let json_of_constr =
    json_of_telescope json_of_arg_spec json_of_tm_sys

  let json_of_body =
    json_of_telescope json_of_tm (json_of_labeled_list json_of_constr)

  let json_of_desc =
    function
    | {kind; lvl; body; status = `Complete} ->
      json_of_body body >>= fun body ->
      ret @@ `A [json_of_kind kind; json_of_lvl lvl; body]
    | {status = `Partial; _} ->
      raise PartialDatatype
end

module RotJson =
struct
  open BasicJson
  open TmJson
  open DescJson
  open RotData

  let json_of_selector sel =
    `A (List.map json_of_string sel)

  let json_of_dep =
    function
    | True -> `String "True"
    | False -> `String "False"
    | Libsum -> `A [`String "Libsum"]
    | Self {stem; redsum} -> `A [`String "Self"; json_of_string stem; json_of_string redsum]
    | Import {sel; stem; rotsum} -> `A [`String "Import"; json_of_selector sel; json_of_string stem; json_of_string rotsum]
    | Shell {cmd; exit} -> `A [`String "Shell"]

  let json_of_ver = json_of_string

  let json_of_datum =
    function
    | P {ty} ->
      json_of_tm ty >>= fun ty ->
      ret @@ `A [`String "p"; ty]

    | Def {ty; tm} ->
      json_of_tm ty >>= fun ty ->
      json_of_tm tm >>= fun tm ->
      ret @@ `A [`String "def"; ty; tm]

    | Desc desc ->
      json_of_desc desc >>= fun desc ->
      ret @@ `A [`String "desc"; desc]

  let json_of_deps l =
    `A (List.map json_of_dep l)

  let json_of_repo =
    json_of_olabeled_list json_of_datum

  let compose_rot ~deps ~repo =
    `A [`String version; deps; repo]
end

open RotData
open RotJson

let datum_of_name global_env name =
  match GlobalEnv.lookup global_env name with
  | `P ty -> P {ty}
  | `Def (ty, tm) -> Def {ty; tm}
  | `Desc desc -> Desc desc
  | `Tw _ | `I ->
    Format.eprintf "Unexpected entry associated with %a.@." Name.pp name;
    invalid_arg "RotIO.repo"

let repo : RotData.repo m =
  assert_top_level >>
  global_env >>= fun global_env ->
  resolver <<@> ResEnv.export_native_globals >>= fun name_table ->
  ret @@ ListUtil.foreach name_table @@
  fun (ostr, name) -> (ostr, datum_of_name global_env name)

let deps : RotData.dep list m =
  mlconf >>=
  function
  | TopModule _ | InStdin _ -> raise ML.WrongMode
  | InFile {stem; redsum; _} ->
    let lib_dep = Libsum in
    let self_dep = Self {stem; redsum} in
    mlenv <<@> ML.Env.imports >>= fun imports ->
    Combinators.flip MU.traverse imports begin fun sel ->
      let stem = FileRes.selector_to_stem stem sel in
      cached_resolver stem >>=
      function
      | Some (_, rotsum) -> ret @@ Import {sel; stem; rotsum}
      | None ->
        Format.eprintf "Module at %s was imported but not in the cache." stem;
        raise Not_found
    end >>= fun import_deps ->
    ret @@ [lib_dep; self_dep] @ import_deps

let write_rot ~scalar_style ~layout_style rot =
  mlconf >>=
  function
  | TopModule _ | InStdin _ -> raise ML.WrongMode
  | InFile {stem; indent; _} ->
    let rotpath = FileRes.stem_to_rot stem in
    let rotstr = Ezjsonm.to_string ~minify:true rot in

    Format.eprintf "@[%sWriting %s.@]@." indent rotpath;
    let channel = open_out_bin rotpath in
    output_string channel rotstr;
    close_out channel;
    Format.eprintf "@[%sWritten %s.@]@." indent rotpath;

    resolver <<@> fun resolver -> resolver, Digest.string rotstr

let write =
  repo >>= json_of_repo >>= fun repo ->
  deps <<@> json_of_deps >>= fun deps ->
  let rot = RotJson.compose_rot deps repo in
  write_rot ~scalar_style:`Any ~layout_style:`Flow rot
