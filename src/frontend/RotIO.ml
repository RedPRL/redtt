open RedBasis
open Bwd
open RedTT_Core
open Contextual

module M = Monad.Notation (Contextual)
open M
module MU = Monad.Util (Contextual)

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
    | `A [a, b] ->
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
    | `Reg -> `String "reg" (* wow! we have "regular" kinds? *)
    | `Kan -> `String "kan"
    | `Pre -> `String "pre"

  let kind_of_json =
    function
    | "reg" -> `Reg
    | "kan" -> `Kan
    | "pre" -> `Pre
    | _ -> raise IllFormed

  let json_of_lvl =
    function
    | `Omega -> `String "omega"
    | `Const i -> json_of_int i

  let lvl_of_json =
    function
    | `String "omega" -> `Omega
    | s -> `Const (int_of_json s)

  let json_of_twin =
    function
    | `Only -> `String "only"
    | `TwinL -> `String "twinl"
    | `TwinR -> `String "twinr"

  let json_of_bnd json_of_bdy (B (nm, bdy)) =
    json_of_bdy bdy >>= fun bdy ->
    ret @@ `A [json_of_ostring nm; bdy]

  let json_of_nbnd json_of_bdy (NB (nms, bdy)) =
    json_of_bdy bdy >>= fun bdy ->
    ret @@ `A [json_of_ostring_bwd nms; bdy]

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
    match ResEnv.id_of_name name res with
    | Some id -> kont_found @@ json_of_int id
    | None ->
      source_stem name >>= function
      | None -> kont_notfound ()
      | Some stem ->
        cached_resolver stem >>= function
        | None ->
          Format.eprintf "Module at %s spread names around without leaving a trace in the cache.@." stem;
          raise @@ Impossible "impossible cache miss"
        | Some (res, _) ->
          match ResEnv.id_of_name name res with
          | None -> kont_notfound ()
          | Some id -> kont_found @@ `A [`String stem; json_of_int id]

  and json_of_meta ~name ~ushift =
    json_of_name name
      (fun () -> expand_meta ~name ~ushift >>= json_of_tm)
      (fun name -> ret @@ `A [`String "meta"; name; json_of_int ushift])

  and json_of_var ~name ~twin ~ushift =
    json_of_name name
      (fun () -> expand_var ~name ~twin ~ushift >>= json_of_tm)
      (fun name -> ret @@ `A [`String "var"; name; json_of_twin twin; json_of_int ushift])

  and json_of_dlbl dlbl =
    json_of_name dlbl (fun () -> raise @@ Impossible "datatype name escaped the serialization context.") ret

  and json_of_tm tm =
    match unleash tm with
    | FHCom {r; r'; cap; sys} ->
      json_of_tm r >>= fun r ->
      json_of_tm r' >>= fun r' ->
      json_of_tm cap >>= fun cap ->
      json_of_tm_bnd_sys sys >>= fun sys ->
      ret @@ `A [`String "fhcom"; r; r'; cap; sys]

    | Univ {kind; lvl} ->
      ret @@ `A [`String "univ"; json_of_kind kind; json_of_lvl lvl]

    | Pi (dom, cod) ->
      json_of_tm dom >>= fun dom ->
      json_of_bnd json_of_tm cod >>= fun cod ->
      ret @@ `A [`String "pi"; dom; cod]

    | Ext ext ->
      json_of_nbnd (json_of_pair (json_of_tm, json_of_tm_sys)) ext >>= fun ext ->
      ret @@ `A [`String "ext"; ext]

    | Restrict face ->
      json_of_tm_face face >>= fun face ->
      ret @@ `A [`String "restrict"; face]

    | Sg (dom, cod) ->
      json_of_tm dom >>= fun dom ->
      json_of_bnd json_of_tm cod >>= fun cod ->
      ret @@ `A [`String "sg"; dom; cod]

    | V {r; ty0; ty1; equiv} ->
      json_of_tm r >>= fun r ->
      json_of_tm ty0 >>= fun ty0 ->
      json_of_tm ty1 >>= fun ty1 ->
      json_of_tm equiv >>= fun equiv ->
      ret @@ `A [`String "v"; r; ty0; ty1; equiv]

    | VIn {r; tm0; tm1} ->
      json_of_tm r >>= fun r ->
      json_of_tm tm0 >>= fun tm0 ->
      json_of_tm tm1 >>= fun tm1 ->
      ret @@ `A [`String "vin"; r; tm0; tm1]

    | Lam (B (nm, tm)) ->
      json_of_tm tm >>= fun tm ->
      ret @@ `A [`String "lam"; json_of_ostring nm; tm]

    | ExtLam extlam ->
      json_of_nbnd json_of_tm extlam >>= fun extlam ->
      ret @@ `A [`String "extlam"; extlam]

    | RestrictThunk face ->
      json_of_tm_face face >>= fun face ->
      ret @@ `A [`String "restrictthunk"; face]

    | Cons (tm0, tm1) ->
      json_of_tm tm0 >>= fun tm0 ->
      json_of_tm tm1 >>= fun tm1 ->
      ret @@ `A [`String "cons"; tm0; tm1]

    | Dim0 -> ret @@ `String "dim0"

    | Dim1 -> ret @@ `String "dim1"

    | Box {r; r'; cap; sys} ->
      json_of_tm r >>= fun r ->
      json_of_tm r' >>= fun r' ->
      json_of_tm cap >>= fun cap ->
      json_of_tm_sys sys >>= fun sys ->
      ret @@ `A [`String "box"; r; r'; cap; sys]

    | Up cmd ->
      json_of_cmd cmd >>= fun cmd ->
      ret @@ `A [`String "up"; cmd]

    | Let (cmd, B (nm, tm)) ->
      json_of_cmd cmd >>= fun cmd ->
      json_of_tm tm >>= fun tm ->
      ret @@ `A [`String "let"; cmd; json_of_ostring nm; tm]

    | Data {lbl; params} ->
      json_of_dlbl lbl >>= fun lbl ->
      json_of_list json_of_tm params >>= fun params ->
      ret @@ `A [`String "data"; lbl; params]

    | Intro (dlbl, clbl, params, args) ->
      json_of_dlbl dlbl >>= fun dlbl ->
      json_of_list json_of_tm params >>= fun params ->
      json_of_list json_of_tm args >>= fun args ->
      ret @@ `A [`String "intro"; dlbl; json_of_string clbl; params; args]

  and json_of_head =
    function
    | Meta {name; ushift} ->
      json_of_meta ~name ~ushift

    | Var {name; twin; ushift} ->
      json_of_var ~name ~twin ~ushift

    | Ix (ix, twin) ->
      ret @@ `A [`String "ix"; json_of_int ix; json_of_twin twin]

    | Down {ty; tm} ->
      json_of_tm ty >>= fun ty ->
      json_of_tm tm >>= fun tm ->
      ret @@ `A [`String "down"; ty; tm]

    | DownX tm ->
      json_of_tm tm >>= fun tm ->
      ret @@ `A [`String "downx"; tm]

    | Coe {r; r'; ty = B (nm, ty); tm} ->
      json_of_tm r >>= fun r ->
      json_of_tm r' >>= fun r' ->
      json_of_tm ty >>= fun ty ->
      json_of_tm tm >>= fun tm ->
      ret @@ `A [`String "coe"; r; r'; json_of_ostring nm; ty; tm]

    | HCom {r; r'; ty; cap; sys} ->
      json_of_tm r >>= fun r ->
      json_of_tm r' >>= fun r' ->
      json_of_tm ty >>= fun ty ->
      json_of_tm cap >>= fun cap ->
      json_of_tm_bnd_sys sys >>= fun sys ->
      ret @@ `A [`String "hcom"; r; r'; ty; cap; sys]

    | Com {r; r'; ty = B (nm, ty); cap; sys} ->
      json_of_tm r >>= fun r ->
      json_of_tm r' >>= fun r' ->
      json_of_tm ty >>= fun ty ->
      json_of_tm cap >>= fun cap ->
      json_of_tm_bnd_sys sys >>= fun sys ->
      ret @@ `A [`String "com"; r; r'; json_of_ostring nm; ty; cap; sys]

    | GHCom {r; r'; ty; cap; sys} ->
      json_of_tm r >>= fun r ->
      json_of_tm r' >>= fun r' ->
      json_of_tm ty >>= fun ty ->
      json_of_tm cap >>= fun cap ->
      json_of_tm_bnd_sys sys >>= fun sys ->
      ret @@ `A [`String "ghcom"; r; r'; ty; cap; sys]

    | GCom {r; r'; ty = B (nm, ty); cap; sys} ->
      json_of_tm r >>= fun r ->
      json_of_tm r' >>= fun r' ->
      json_of_tm ty >>= fun ty ->
      json_of_tm cap >>= fun cap ->
      json_of_tm_bnd_sys sys >>= fun sys ->
      ret @@ `A [`String "gcom"; r; r'; json_of_ostring nm; ty; cap; sys]

  and json_of_frame =
    function
    | Fst -> ret @@ `String "fst"

    | Snd -> ret @@ `String "snd"

    | FunApp arg ->
      json_of_tm arg >>= fun arg ->
      ret @@ `A [`String "funapp"; arg]

    | ExtApp rs ->
      json_of_list json_of_tm rs >>= fun rs ->
      ret @@ `A [`String "extapp"; rs]

    | VProj {r; func} ->
      json_of_tm r >>= fun r ->
      json_of_tm func >>= fun func ->
      ret @@ `A [`String "vproj"; r; func]

    | Cap {r; r'; ty; sys} ->
      json_of_tm r >>= fun r ->
      json_of_tm r' >>= fun r' ->
      json_of_tm ty >>= fun ty ->
      json_of_tm_bnd_sys sys >>= fun sys ->
      ret @@ `A [`String "cap"; r; r'; ty; sys]

    | RestrictForce -> ret @@ `String "restrictforce"

    | Elim {dlbl; params; mot; clauses} ->
      json_of_dlbl dlbl >>= fun dlbl ->
      json_of_list json_of_tm params >>= fun params ->
      json_of_bnd json_of_tm mot >>= fun mot ->
      json_of_labeled_list (json_of_nbnd json_of_tm) clauses >>= fun clauses ->
      ret @@ `A [`String "elim"; dlbl; params; mot; clauses]

  and json_of_cmd cmd =
    json_of_pair (json_of_head, json_of_list json_of_frame) cmd

  and json_of_tm_face f = json_of_face json_of_tm json_of_tm f
  and json_of_tm_sys s = json_of_list json_of_tm_face s

  and json_of_tm_bnd_face f = json_of_face json_of_tm (json_of_bnd json_of_tm) f
  and json_of_tm_bnd_sys s = json_of_list json_of_tm_bnd_face s
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
    | True -> `String "true"
    | False -> `String "false"
    | Libsum -> `A [`String "libsum"]
    | Self {stem; redsum} -> `A [`String "selfloc"; json_of_string stem; json_of_string redsum]
    | Import {sel; stem; rotsum} -> `A [`String "moduleloc"; json_of_selector sel; json_of_string stem; json_of_string rotsum]
    | Shell {cmd; exit} -> `A [`String "shell"]

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
