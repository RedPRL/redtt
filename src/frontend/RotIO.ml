open RedBasis
open Bwd
open RedTT_Core
open Contextual

module M = Monad.Notation (Contextual)
open M
module MU = Monad.Util (Contextual)
module J = Ezjsonm

(* Tm *)

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
    | j -> J.parse_error j "int_of_json"

  let json_of_string s = `String s

  let string_of_json =
    function
    | `String s -> s
    | j -> J.parse_error j "string_of_json"

  let json_of_ostring =
    function
    | None -> `Null
    | Some str -> `String str

  let ostring_of_json =
    function
    | `Null -> None
    | `String str -> Some str
    | j -> J.parse_error j "ostring_of_json"

  let json_of_list json_of_item l =
    MU.traverse json_of_item l <<@> fun l -> `A l

  let list_of_json item_of_json =
    function
    | `A l -> MU.traverse item_of_json l
    | j -> J.parse_error j "list_of_json"

  (* pure version *)
  let json_of_list_ json_of_item l =
    `A (List.map json_of_item l)

  (* pure version *)
  let list_of_json_ item_of_json =
    function
    | `A l -> List.map item_of_json l
    | j -> J.parse_error j "list_of_json_"

  let json_of_ostring_bwd nms =
    json_of_list_ json_of_ostring @@ Bwd.to_list nms

  let ostring_bwd_of_json l =
    Bwd.from_list @@ list_of_json_ ostring_of_json l

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
    | j -> J.parse_error j "pair_of_json"

  let json_of_labeled (json_of_a, json_of_b) (a, b) =
    json_of_b b >>= fun b ->
    ret @@ `A [json_of_a a; b]

  let labeled_of_json (a_of_json, b_of_json) =
    function
    | `A [a; b] ->
      b_of_json b >>= fun b ->
      ret @@ (a_of_json a, b)
    | j -> J.parse_error j "labeled_of_json"

  (* labeled in reverse *)
  let json_of_delebal (json_of_a, json_of_b) (a, b) =
    json_of_a a >>= fun a ->
    ret @@ `A [a; json_of_b b]

  (* labeled in reverse *)
  let delebal_of_json (a_of_json, b_of_json) =
    function
    | `A [a; b] ->
      a_of_json a >>= fun a ->
      ret @@ (a, b_of_json b)
    | j -> J.parse_error j "delebal_of_json"

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
    | ty, Some def ->
      ret @@ Down {ty = shift_univ ushift ty; tm = shift_univ ushift def}

  let expand_var ~name ~ushift ~twin =
    global_env >>= fun genv ->
    match GlobalEnv.lookup_with_twin genv name twin with
    | _, None ->
      Format.eprintf "Variable %a is not expandable.@." Name.pp name;
      raise @@ Impossible "Some variable escapes the serialization context."
    | ty, Some def ->
      ret @@ Down {ty = shift_univ ushift ty; tm = shift_univ ushift def}

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
    | j -> J.parse_error j "kind_of_json"

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
    | j -> J.parse_error j "twin_of_json"

  let json_of_bnd json_of_bdy (B (nm, bdy)) =
    json_of_bdy bdy >>= fun bdy ->
    ret @@ `A [json_of_ostring nm; bdy]

  let bnd_of_json bdy_of_json =
    function
    | `A [nm; bdy] ->
      bdy_of_json bdy >>= fun bdy ->
      ret @@ (B (ostring_of_json nm, bdy))
    | j -> J.parse_error j "bnd_of_json"

  let json_of_nbnd json_of_bdy (NB (nms, bdy)) =
    json_of_bdy bdy >>= fun bdy ->
    ret @@ `A [json_of_ostring_bwd nms; bdy]

  let nbnd_of_json bdy_of_json =
    function
    | `A [nms; bdy] ->
      bdy_of_json bdy >>= fun bdy ->
      ret @@ (NB (ostring_bwd_of_json nms, bdy))
    | j -> J.parse_error j "nbnd_of_json"

  let json_of_face json_of_r json_of_bdy (r, r', bdy) =
    json_of_r r >>= fun r ->
    json_of_r r' >>= fun r' ->
    json_of_bdy bdy >>= fun bdy ->
    ret @@ `A [r; r'; bdy]

  let face_of_json r_of_json bdy_of_json =
    function
    | `A [r; r'; bdy] ->
      r_of_json r >>= fun r ->
      r_of_json r' >>= fun r' ->
      bdy_of_json bdy >>= fun bdy ->
      ret (r, r', bdy)
    | j -> J.parse_error j "face_of_json"

  let rec json_of_foreign_name name kont_notfound kont_found =
    source_stem name >>= function
    | None -> kont_notfound ()
    | Some stem ->
      retrieve_module stem >>= function
      | None ->
        Format.eprintf "Module at %s spread names around without leaving a trace in the cache.@." stem;
        raise @@ Impossible "impossible cache miss"
      | Some (res, _) ->
        match ResEnv.native_of_name name res with
        | None -> kont_notfound ()
        | Some native -> kont_found @@ `A [`String stem; json_of_int native]

  and json_of_name name kont_notfound kont_found =
    resolver >>= fun res ->
    match ResEnv.native_of_name name res with
    | Some native -> kont_found @@ json_of_int native
    | None -> json_of_foreign_name name kont_notfound kont_found

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
      json_of_tm_bnd cod >>= fun cod ->
      ret @@ `A [`String "Pi"; dom; cod]

    | Ext ext ->
      json_of_nbnd (json_of_pair (json_of_tm, json_of_tm_sys)) ext >>= fun ext ->
      ret @@ `A [`String "Ext"; ext]

    | Restrict face ->
      json_of_tm_face face >>= fun face ->
      ret @@ `A [`String "restrict"; face]

    | Sg (dom, cod) ->
      json_of_tm dom >>= fun dom ->
      json_of_tm_bnd cod >>= fun cod ->
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
      json_of_tm_bnd lam >>= fun lam ->
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
      json_of_tm_bnd bnd >>= fun bnd ->
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

    | FortyTwo -> ret @@ `String "FortyTwo"

  and json_of_tm_bnd bnd = json_of_bnd json_of_tm bnd

  and json_of_head =
    function
    | Meta {name; ushift} ->
      json_of_name name
        (fun () -> expand_meta ~name ~ushift >>= json_of_head)
        (fun name -> ret @@ `A [`String "Meta"; name; json_of_int ushift])

    | Var {name; twin; ushift} ->
      json_of_name name
        (fun () -> expand_var ~name ~twin ~ushift >>= json_of_head)
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
      json_of_tm_bnd ty >>= fun ty ->
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
      json_of_tm_bnd ty >>= fun ty ->
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
      json_of_tm_bnd ty >>= fun ty ->
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

    | VProj {r; ty0; ty1; func} ->
      json_of_tm r >>= fun r ->
      json_of_tm ty0 >>= fun ty0 ->
      json_of_tm ty1 >>= fun ty1 ->
      json_of_tm func >>= fun func ->
      ret @@ `A [`String "VProj"; r; ty0; ty1; func]

    | Cap {r; r'; ty; sys} ->
      json_of_tm r >>= fun r ->
      json_of_tm r' >>= fun r' ->
      json_of_tm ty >>= fun ty ->
      json_of_tm_bnd_sys sys >>= fun sys ->
      ret @@ `A [`String "Cap"; r; r'; ty; sys]

    | RestrictForce -> ret @@ `String "RestrictForce"

    | Elim {dlbl; params; mot; clauses} ->
      let json_of_clause = json_of_labeled (json_of_string, json_of_nbnd json_of_tm) in
      json_of_dlbl dlbl >>= fun dlbl ->
      json_of_list json_of_tm params >>= fun params ->
      json_of_tm_bnd mot >>= fun mot ->
      json_of_list json_of_clause clauses >>= fun clauses ->
      ret @@ `A [`String "Elim"; dlbl; params; mot; clauses]

  and json_of_cmd cmd =
    json_of_pair (json_of_head, json_of_list json_of_frame) cmd

  and json_of_tm_face face = json_of_face json_of_tm json_of_tm face
  and json_of_tm_sys sys = json_of_list json_of_tm_face sys

  and json_of_tm_bnd_face face = json_of_face json_of_tm json_of_tm_bnd face
  and json_of_tm_bnd_sys sys = json_of_list json_of_tm_bnd_face sys

  let rec foreign_name_of_json : J.value -> Name.t m =
    function
    | `A [`String stem; native] as j ->
      retrieve_module stem >>= begin
        function
        | None -> J.parse_error j "foreign_name_of_json"
        | Some (res, _) ->
          match ResEnv.name_of_native (int_of_json native) res with
          | None -> J.parse_error j "foreign_name_of_json"
          | Some name -> ret name
      end
    | j -> J.parse_error j "foreign_name_of_json"

  let rec name_of_json : J.value -> Name.t m =
    function
    | `String native as j ->
      resolver >>= fun res ->
      let native = int_of_json (`String native) in
      begin match ResEnv.name_of_native native res with
        | None -> J.parse_error j "name_of_json (native = %i)" native
        | Some name -> ret name
      end
    | x -> foreign_name_of_json x

  and dlbl_of_json json = name_of_json json

  and tm_of_json json : tm m =
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
      tm_bnd_of_json cod >>= fun cod ->
      ret @@ Pi (dom, cod)

    | `A [`String "Ext"; ext] ->
      nbnd_of_json (pair_of_json (tm_of_json, tm_sys_of_json)) ext >>= fun ext ->
      ret @@ Ext ext

    | `A [`String "Restrict"; face] ->
      tm_face_of_json face >>= fun face ->
      ret @@ Restrict face

    | `A [`String "Sg"; dom; cod] ->
      tm_of_json dom >>= fun dom ->
      tm_bnd_of_json cod >>= fun cod ->
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
      tm_bnd_of_json lam >>= fun lam ->
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
      tm_bnd_of_json bnd >>= fun bnd ->
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

    | `String "FortyTwo" -> ret FortyTwo

    | j -> J.parse_error j "tm_of_json"

  and tm_bnd_of_json bnd = bnd_of_json tm_of_json bnd

  and head_of_json =
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
      tm_bnd_of_json ty >>= fun ty ->
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
      tm_bnd_of_json ty >>= fun ty ->
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
      tm_bnd_of_json ty >>= fun ty ->
      tm_of_json cap >>= fun cap ->
      tm_bnd_sys_of_json sys >>= fun sys ->
      ret @@ GCom {r; r'; ty; cap; sys}

    | j -> J.parse_error j "head_of_json"

  and frame_of_json =
    function
    | `String "Fst" -> ret Fst

    | `String "Snd" -> ret Snd

    | `A [`String "FunApp"; arg] ->
      tm_of_json arg >>= fun arg ->
      ret @@ FunApp arg

    | `A [`String "ExtApp"; rs] ->
      list_of_json tm_of_json rs >>= fun rs ->
      ret @@ ExtApp rs

    | `A [`String "VProj"; r; ty0; ty1; func] ->
      tm_of_json r >>= fun r ->
      tm_of_json ty0 >>= fun ty0 ->
      tm_of_json ty1 >>= fun ty1 ->
      tm_of_json func >>= fun func ->
      ret @@ VProj {r; ty0; ty1; func}

    | `A [`String "Cap"; r; r'; ty; sys] ->
      tm_of_json r >>= fun r ->
      tm_of_json r' >>= fun r' ->
      tm_of_json ty >>= fun ty ->
      tm_bnd_sys_of_json sys >>= fun sys ->
      ret @@ Cap {r; r'; ty; sys}

    | `String "RestrictForce" -> ret RestrictForce

    | `A [`String "Elim"; dlbl; params; mot; clauses] ->
      let clause_of_json = labeled_of_json (string_of_json, nbnd_of_json tm_of_json) in
      dlbl_of_json dlbl >>= fun dlbl ->
      list_of_json tm_of_json params >>= fun params ->
      tm_bnd_of_json mot >>= fun mot ->
      list_of_json clause_of_json clauses >>= fun clauses ->
      ret @@ Elim {dlbl; params; mot; clauses}

    | j -> J.parse_error j "frame_of_json"

  and cmd_of_json cmd =
    pair_of_json (head_of_json, list_of_json frame_of_json) cmd

  and tm_face_of_json face = face_of_json tm_of_json tm_of_json face
  and tm_sys_of_json sys = list_of_json tm_face_of_json sys

  and tm_bnd_face_of_json face = face_of_json tm_of_json tm_bnd_of_json face
  and tm_bnd_sys_of_json sys = list_of_json tm_bnd_face_of_json sys
end

module DescJson =
struct
  open BasicJson
  open TmJson
  open Desc

  let json_of_rec_spec =
    function
    | Self -> ret @@ `String "Self"

  let rec_spec_of_json =
    function
    | `String "Self" -> ret Self
    | j -> J.parse_error j "rec_spec_of_json"

  let json_of_arg_spec =
    function
    | `Const tm ->
      json_of_tm tm >>= fun tm ->
      ret @@ `A [`String "Const"; tm]

    | `Rec rec_spec ->
      json_of_rec_spec rec_spec >>= fun rec_spec ->
      ret @@ `A [`String "Rec"; rec_spec]

    | `Dim -> ret @@ `String "Dim"

  let arg_spec_of_json =
    function
    | `A [`String "Const"; tm] ->
      tm_of_json tm >>= fun tm ->
      ret @@ `Const tm

    | `A [`String "Rec"; rec_spec] ->
      rec_spec_of_json rec_spec >>= fun rec_spec ->
      ret @@ `Rec rec_spec

    | `String "Dim" -> ret `Dim

    | j -> J.parse_error j "arg_spec_of_json"

  (* MORTALITY there's a better encoding *)
  let rec json_of_telescope json_of_a json_of_e =
    function
    | TNil e ->
      json_of_e e >>= fun e ->
      ret @@ `A [e]
    | TCons (a, tel) ->
      json_of_a a >>= fun a ->
      json_of_bnd (json_of_telescope json_of_a json_of_e) tel >>= fun tel ->
      ret @@ `A [a; tel]

  let rec telescope_of_json a_of_json e_of_json =
    function
    | `A [e] ->
      e_of_json e >>= fun e ->
      ret @@ TNil e
    | `A [a; tel] ->
      a_of_json a >>= fun a ->
      bnd_of_json (telescope_of_json a_of_json e_of_json) tel >>= fun tel ->
      ret @@ TCons (a, tel)
    | j -> J.parse_error j "telescope_of_json"

  let json_of_constr =
    json_of_telescope json_of_arg_spec json_of_tm_sys

  let constr_of_json =
    telescope_of_json arg_spec_of_json tm_sys_of_json

  let json_of_constrs =
    json_of_list @@ json_of_labeled (json_of_string, json_of_constr)

  let constrs_of_json =
    list_of_json @@ labeled_of_json (string_of_json, constr_of_json)

  let json_of_body =
    json_of_telescope json_of_tm json_of_constrs

  let body_of_json =
    telescope_of_json tm_of_json constrs_of_json

  let json_of_desc =
    function
    | {kind; lvl; body; status = `Complete} ->
      json_of_body body >>= fun body ->
      ret @@ `A [json_of_kind kind; json_of_lvl lvl; body]
    | {status = `Partial; _} ->
      raise PartialDatatype

  let desc_of_json : _ -> desc m =
    function
    | `A [kind; lvl; body] ->
      body_of_json body >>= fun body ->
      ret @@ {kind = kind_of_json kind; lvl = lvl_of_json lvl; body; status = `Complete}
    | j -> J.parse_error j "desc_of_json"
end

module RotJson =
struct
  open BasicJson
  open TmJson
  open DescJson
  open RotData

  let json_of_selector =
    json_of_list_ json_of_string

  let selector_to_json =
    list_of_json_ string_of_json

  let json_of_digest d =
    `String (Digest.to_hex d)

  let digest_of_json =
    function
    | `String h as j -> begin try Digest.from_hex h with Invalid_argument _ -> J.parse_error j "digest_of_json" end
    | j -> J.parse_error j "digest_of_json"

  let json_of_dep =
    function
    | True -> `String "True"
    | False -> `String "False"
    | Libsum -> `A [`String "Libsum"]
    | Self {stem; redsum} -> `A [`String "Self"; json_of_string stem; json_of_digest redsum]
    | Import {sel; stem; rotsum} -> `A [`String "Import"; json_of_selector sel; json_of_string stem; json_of_digest rotsum]
    | Shell {cmd; exit} -> `A [`String "Shell"; json_of_string cmd; json_of_int exit]

  let dep_of_json =
    function
    | `String "True" -> True
    | `String "False" -> False
    | `A [`String "Libsum"] -> Libsum
    | `A [`String "Self"; stem; redsum] ->
      Self {stem = string_of_json stem; redsum = digest_of_json redsum}
    | `A [`String "Import"; sel; stem; rotsum] ->
      Import {sel = selector_to_json sel; stem = string_of_json stem; rotsum = digest_of_json rotsum}
    | `A [`String "Shell"; cmd; exit] -> Shell {cmd =string_of_json cmd; exit = int_of_json exit}
    | j -> J.parse_error j "dep_of_json"


  let json_of_ver = json_of_string

  let ver_of_json = string_of_json

  let json_of_entry : entry -> J.value m =
    function
    | `P ty ->
      json_of_tm ty >>= fun ty ->
      ret @@ `A [`String "P"; ty]

    | `Def (ty, tm) ->
      json_of_tm ty >>= fun ty ->
      json_of_tm tm >>= fun tm ->
      ret @@ `A [`String "Def"; ty; tm]

    | `Desc desc ->
      json_of_desc desc >>= fun desc ->
      ret @@ `A [`String "Desc"; desc]

    | `Tw (ty0, ty1) ->
      json_of_tm ty0 >>= fun ty0 ->
      json_of_tm ty1 >>= fun ty1 ->
      ret @@ `A [`String "Tw"; ty0; ty1]

    | `I ->
      ret @@ `String "I"

  let entry_of_json : J.value -> entry m =
    function
    | `A [`String "P"; ty] ->
      tm_of_json ty >>= fun ty ->
      ret @@ `P ty

    | `A [`String "Def"; ty; tm] ->
      tm_of_json ty >>= fun ty ->
      tm_of_json tm >>= fun tm ->
      ret @@ `Def (ty, tm)

    | `A [`String "Desc"; desc] ->
      desc_of_json desc >>= fun desc ->
      ret @@ `Desc desc

    | `A [`String "Tw"; ty0; ty1] ->
      tm_of_json ty0 >>= fun ty0 ->
      tm_of_json ty1 >>= fun ty1 ->
      ret @@ `Tw (ty0, ty1)

    | `String "I" -> ret `I

    | j -> J.parse_error j "entry_of_json"

  let json_of_rigidity =
    function
    | None -> `Null
    | Some `Rigid -> `String "Rigid"
    | Some `Flex -> `String "Flex"

  let rigidity_of_json =
    function
    | `Null -> None
    | `String "Rigid" -> Some `Rigid
    | `String "Flex" -> Some `Flex
    | j -> J.parse_error j "rigidity_of_json"

  let json_of_info =
    json_of_delebal (json_of_entry, json_of_rigidity)

  let info_of_json =
    delebal_of_json (entry_of_json, rigidity_of_json)

  let json_of_deps =
    json_of_list_ json_of_dep

  let deps_of_json =
    list_of_json_ dep_of_json

  let json_of_repo =
    json_of_list @@ json_of_labeled (json_of_ostring, json_of_info)

  (*
  let repo_of_json =
    olabeled_list_o
  let repo_of_json =
    olabeled_list_of_json entry_of_json
  *)
  let raw_repo_of_json =
    list_of_json @@ labeled_of_json (ostring_of_json, ret)

  let json_of_foreign name =
    json_of_foreign_name name (fun () -> invalid_arg "json_of_foreign") ret

  let foreign_of_json =
    foreign_name_of_json

  let json_of_reexported : reexported -> J.value m =
    json_of_list json_of_foreign

  let raw_reexported_of_json =
    list_of_json ret

  let json_of_rot ~deps ~reexported ~repo =
    json_of_reexported reexported >>= fun reexported ->
    json_of_repo repo >>= fun repo ->
    ret @@ `A [`String version; json_of_deps deps; reexported; repo]

  (* everything decoded except repo *)
  let decompose_rot =
    function
    | `A [`String v; deps; reexported; repo] when String.equal v version ->
      raw_reexported_of_json reexported >>= fun reexported ->
      raw_repo_of_json repo >>= fun raw_repo ->
      ret (deps_of_json deps, reexported, raw_repo)
    | j -> J.parse_error (J.unwrap j) "decompose_rot"
end

module Writer =
struct
  open RotData

  let deps : RotData.dep list m =
    mlconf >>=
    function
    | TopModule _ | InMem _ -> raise ML.WrongMode
    | InFile {stem; redsum; _} ->
      let lib_dep = Libsum in
      let self_dep = Self {stem; redsum} in
      mlenv <<@> ML.Env.imports >>= fun imports ->
      Combinators.flip MU.traverse imports begin fun sel ->
        let stem = FileRes.selector_to_stem stem sel in
        retrieve_module stem >>=
        function
        | Some (_, rotsum) -> ret @@ Import {sel; stem; rotsum}
        | None ->
          Format.eprintf "Module at %s was imported but not in the cache." stem;
          raise Not_found
      end >>= fun import_deps ->
      ret @@ [lib_dep; self_dep] @ import_deps

  let repo : RotData.repo m =
    assert_top_level >>
    resolver <<@> ResEnv.export_native_globals >>= fun name_table ->
    Combinators.flip MU.traverse name_table @@
    fun (ostr, name) -> lookup_top name <<@> fun info -> (ostr, info)

  let reexported : RotData.reexported m =
    assert_top_level >>
    resolver <<@> ResEnv.export_foreign_globals

  let encode rot = Ezgzip.compress (J.to_string ~minify:true rot)

  let write_rot rot =
    mlconf >>=
    function
    | TopModule _ | InMem _ -> raise ML.WrongMode
    | InFile {stem; indent; _} ->
      let rotpath = FileRes.stem_to_rot stem in
      let rotstr = encode rot in

      let channel = open_out_bin rotpath in
      begin
        match output_string channel rotstr with
        | () -> close_out channel
        | exception exn -> close_out channel; raise exn
      end;

      resolver <<@> fun resolver -> resolver, Digest.string rotstr

  let write =
    deps >>= fun deps ->
    reexported >>= fun reexported ->
    repo >>= fun repo ->
    RotJson.json_of_rot deps reexported repo >>= write_rot
end

let write = Writer.write

module Reader =
struct
  open RotData
  open RotJson

  let check_dep ~redsum:true_redsum ~importer ~stem:true_stem =
    function
    | True -> ret true
    | False -> ret false
    | Libsum -> ret true
    | Self {stem; redsum} ->
      if String.equal stem true_stem then
        let true_redsum = match true_redsum with None -> Digest.file (FileRes.stem_to_red stem) | Some rs -> rs in
        ret @@ Digest.equal redsum true_redsum
      else
        ret false
    | Import {sel; stem; rotsum} ->
      let true_stem = FileRes.selector_to_stem ~stem:true_stem sel in
      if String.equal true_stem stem then
        importer ~selector:sel >>=
        function
        | _, lib_digest -> ret @@ Digest.equal rotsum lib_digest
      else
        ret false
    | Shell {cmd; exit} ->
      match !unsafe_mode with
      | true -> ret begin Sys.command cmd = exit end
      | false ->
        Log.pp_message ~loc:None ~lvl:`Error Format.pp_print_string Format.std_formatter
          "The rot file wishes to run a commend but the request was rejected.";
        ret false

  (* MORTAL where is the monadic version of [for_all]? *)
  let check_deps ~redsum ~importer ~stem =
    let step prefix dep = if prefix then check_dep ~redsum ~importer ~stem dep else ret false in
    MU.fold_left step true

  let restore_repo ~stem raw_repo =
    ret raw_repo >>=
    (* we need to put the names into the resolver first in order to
       reconstruct recursive stuff (ex: datatypes) *)
    MU.traverse begin
      fun (ostr, raw_info) ->
        let name = Name.named ostr in
        modify_top_resolver @@ ResEnv.add_native_global ~visibility:`Public name >>
        ret (name, raw_info)
    end >>=
    MU.iter begin
      fun (name, raw_info) ->
        info_of_json raw_info >>= restore_top name ~stem
    end

  let restore_reexport =
    MU.iter begin
      fun raw_name ->
        foreign_of_json raw_name >>= function name ->
          modify_top_resolver @@ ResEnv.import_global ~visibility:`Public name
    end

  exception Gzip of Ezgzip.error

  let read_rot ~stem : J.t m =
    let rotpath = FileRes.stem_to_rot stem in
    mlconf <<@> ML.Env.indent >>= fun indent ->

    let channel = open_in_bin rotpath in
    let zipped_rot =
      let bytes_size = 4096 in
      let bytes = Bytes.create bytes_size in
      let raw_rot = Buffer.create (16 * bytes_size) in
      let rec read () =
        let n = input channel bytes 0 (Bytes.length bytes) in
        if n = 0 then
          Buffer.contents raw_rot
        else begin
          Buffer.add_subbytes raw_rot bytes 0 n;
          read ()
        end
      in
      read ()
    in

    match Ezgzip.decompress zipped_rot with
    | Ok rot -> ret (J.from_string rot)
    | Error (`Gzip err) -> raise @@ Gzip err

  let try_read_ ~redsum ~importer ~stem =
    assert_top_level >>
    mlconf <<@> ML.Env.indent >>= fun indent ->
    read_rot ~stem >>= function
    | rot ->
      decompose_rot rot >>= fun (deps, reexported, repo) ->
      let mlconf = ML.InMem {stem; indent} in
      isolate_module ~mlconf begin
        check_deps ~redsum ~importer ~stem deps >>= function
        | false ->
          ret None
        | true ->
          restore_reexport reexported >>
          restore_repo ~stem repo >>
          resolver >>= fun resolver ->
          ret (Some (resolver, Digest.string (Writer.encode rot)))
      end

  let try_read ~redsum ~importer ~stem =
    try_ (try_read_ ~redsum ~importer ~stem) @@
    function
    | Sys_error _ | Gzip _ | J.Parse_error _ -> ret None
    | exn -> raise exn
end

let try_read = Reader.try_read
