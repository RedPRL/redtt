type ty = Tm.chk Tm.t
type tm = Tm.chk Tm.t

module V = Val

type dev =
  | Ask of {ty : ty; body : dev}
  | Guess of {ty : ty; guess : dev; body : dev}
  | Lam of {ty : ty; body : dev}
  | Ret of tm

exception Impure
let purify : dev -> tm =
  failwith ""

let inst0 : tm -> dev -> dev =
  failwith ""

module M :
sig
  include Monad.S

  val up : unit m
  val down : unit m
  val right : unit m
  val left : unit m

  val solve : unit m
end =
struct
  type seq = {cx : Typing.cx; ty : V.value}
  type frame =
    | KGuessL of {ty : ty; seq : seq; body : dev}
    | KGuessR of {ty : ty; seq : seq; guess : dev}
    | KLam of {ty : ty; seq : seq}
    | KAsk of {ty : ty; seq : seq}

  type stack = frame list

  type state = {seq : seq; dev : dev; stk: stack}
  type 'a m = state -> 'a * state
  let ret _ = failwith ""
  let bind _ _ = failwith ""


  let up : unit m =
    fun {dev; stk; _} ->
      match stk with
      | [] ->
        failwith "up"
      | KGuessL frm :: stk ->
        let guess = Guess {ty = frm.ty; guess = dev; body = frm.body} in
        (), {seq = frm.seq; dev = guess; stk}
      | KGuessR frm :: stk ->
        let guess = Guess {ty = frm.ty; guess = frm.guess; body = dev} in
        (), {seq = frm.seq; dev = guess; stk}
      | KLam frm :: stk ->
        let lam = Lam {ty = frm.ty; body = dev} in
        (), {seq = frm.seq; dev = lam; stk}
      | KAsk frm :: stk ->
        let ask = Ask {ty = frm.ty; body = dev} in
        (), {seq = frm.seq; dev = ask; stk}

  let down : unit m =
    fun {seq; dev; stk} ->
      match dev with
      | Ret _ ->
        failwith "down"
      | Ask info ->
        let hole_vty = Typing.Cx.eval seq.cx info.ty in
        let cxx, _ = Typing.Cx.ext_ty ~nm:None seq.cx hole_vty in
        let stk' = KAsk {seq; ty = info.ty} :: stk in
        (), {seq = {seq with cx = cxx}; dev = info.body; stk = stk'}
      | Guess info ->
        let hole_vty = Typing.Cx.eval seq.cx info.ty in
        let cxx, _ = Typing.Cx.ext_ty ~nm:None seq.cx hole_vty in
        let stk' = KGuessL {seq; ty = info.ty; body = info.body} :: stk in
        (), {seq = {seq with cx = cxx}; dev = info.guess; stk = stk'}
      | Lam info ->
        let vty = Typing.Cx.eval seq.cx info.ty in
        let cxx, _ = Typing.Cx.ext_ty ~nm:None seq.cx vty in
        let stk' = KLam {seq; ty = info.ty} :: stk in
        (), {seq = {seq with cx = cxx}; dev = info.body; stk = stk'}

  let right : unit m =
    fun {dev; stk; _} ->
      match stk with
      | KGuessL frm :: stk ->
        let vty = Typing.Cx.eval frm.seq.cx frm.ty in
        let stk' = KGuessR {ty = frm.ty; seq = frm.seq; guess = dev} :: stk in
        (), {seq = {cx = frm.seq.cx; ty = vty}; dev = frm.body; stk = stk'}
      | _ ->
        failwith "right"

  let left : unit m =
    fun {dev; stk; _} ->
      match stk with
      | KGuessR frm :: stk ->
        let vty = Typing.Cx.eval frm.seq.cx frm.ty in
        let stk' = KGuessL {ty = frm.ty; seq = frm.seq; body = dev} :: stk in
        let cxx, _ = Typing.Cx.ext_ty frm.seq.cx ~nm:None vty in
        (), {seq = {cx = cxx; ty = frm.seq.ty}; dev = frm.guess; stk = stk'}
      | _ ->
        failwith "left"

  let solve {seq; dev; stk} =
    match dev with
    | Guess {ty; guess; body} ->
      let tm = purify guess in
      let vty = Typing.Cx.eval seq.cx ty in
      Typing.check seq.cx vty tm;
      (), {seq; dev = inst0 tm body; stk}
    | _ ->
      failwith "solve"

end


