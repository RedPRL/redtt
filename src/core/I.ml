type atom = Name.t

type 'a f =
  [ `Dim0
  | `Dim1
  | `Atom of 'a
  ]

let map f =
  function
  | `Dim0 -> `Dim0
  | `Dim1 -> `Dim1
  | `Atom a -> `Atom (f a)

let bind m k =
  match m with
  | `Dim0 -> `Dim0
  | `Dim1 -> `Dim1
  | `Atom a -> k a

type t = atom f

type action =
  | Subst of t * atom
  | Swap of atom * atom
  | Idn
  | Cmp of action * action

let idn = Idn
let swap a b = Swap (a, b)
let subst r a = Subst (r, a)

let cmp phi1 phi0 =
  match phi1, phi0 with
  | Idn, _ -> phi0
  | _, Idn -> phi1
  | _ -> Cmp (phi1, phi0)


exception Inconsistent

let equate r0 r1 =
  match r0, r1 with
  | `Dim0, `Dim0 ->
    Idn
  | `Dim1, `Dim1 ->
    Idn
  | `Dim0, `Dim1 ->
    raise Inconsistent
  | `Dim1, `Dim0 ->
    raise Inconsistent
  | `Atom a, (`Dim0 | `Dim1) ->
    Subst (r1, a)
  | (`Dim0 | `Dim1), `Atom a ->
    Subst (r0, a)
  | `Atom a, `Atom b when a < b ->
    Subst (r0, b)
  | `Atom a, `Atom b when a > b ->
    Subst (r1, a)
  | `Atom _, `Atom _ ->
    Idn

let act_clock = ref 0.

let _ =
  Diagnostics.on_termination @@ fun _ ->
  Format.eprintf "[diagnostic]: spent %fs acting on dimensions@." !act_clock

let rec act phi =
  function
  | (`Dim0 | `Dim1) as r -> r
  | `Atom a as r ->
    match phi with
    | Idn -> r
    | Swap (b, c) when a = b -> `Atom c
    | Swap (b, c) when a = c -> `Atom b
    | Subst (s, b) when a = b -> s
    | Cmp (psi1, psi0) -> act psi1 @@ act psi0 r
    | _ -> r

let act phi r =
  let now0 = Unix.gettimeofday () in
  let r' = act phi r in
  let now1 = Unix.gettimeofday () in
  act_clock := !act_clock +. (now1 -. now0);
  r'




type compare =
  [ `Same
  | `Apart
  | `Indet
  ]

let compare r r' =
  match r, r' with
  | `Dim0, `Dim0 ->
    `Same
  | `Dim1, `Dim1 ->
    `Same
  | `Dim0, `Dim1 ->
    `Apart
  | `Dim1, `Dim0 ->
    `Apart
  | `Atom x, `Atom y ->
    if x = y then `Same else `Indet
  | `Atom _, _ ->
    `Indet
  | _, `Atom _ ->
    `Indet

let absent x r =
  match r with
  | `Dim0 -> true
  | `Dim1 -> true
  | `Atom y -> x <> y


let pp fmt =
  function
  | `Dim0 ->
    Format.fprintf fmt "0"
  | `Dim1 ->
    Format.fprintf fmt "1"
  | `Atom x ->
    Name.pp fmt x


let rec pp_action fmt =
  function
  | Idn ->
    Format.fprintf fmt "idn"
  | Swap (a, b) ->
    Format.fprintf fmt "%a <-> %a" Name.pp a Name.pp b
  | Subst (r, x) ->
    Format.fprintf fmt "[%a/%a]" pp r Name.pp x
  | Cmp (phi1, phi0) ->
    Format.fprintf fmt "%a %a %a" pp_action phi1 Uuseg_string.pp_utf_8 "∘" pp_action phi0
