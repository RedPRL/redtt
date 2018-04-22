type mcx = MCx.t
type lcx = LCx.t
type rnv = ResEnv.t
type menv = MEnv.t
type hole = Symbol.t

module E = ElabMonad
let (>>=) = E.(>>=)
let (>>) = E.(>>)

(* Some preliminary sketches of the elaborator tactics. *)

let lambda x : hole -> hole E.m =
  fun alpha ->
    E.lookup_goal alpha >>= fun (cx, rnv, ty) ->
    match Tm.out ty with
    | Tm.Pi (dom, Tm.B cod) -> 
      E.eval (LCx.env cx) dom >>= fun vdom ->
      let cx' = LCx.ext cx vdom in
      let goal = MCx.{lcx = cx'; rnv = ResEnv.bind x rnv; ty = cod; cell = Ask} in
      E.new_goal goal >>= fun beta ->
      let tm = 
        let inf = Tm.into @@ Tm.Meta (beta, Tm.Sub (Tm.Id, Tm.into @@ Tm.Var 0)) in
        let chk = Tm.into @@ Tm.Up inf in
        Tm.into @@ Tm.Lam (Tm.B chk)
      in
      E.fill alpha tm >>
      E.ret beta

    | _ -> 
      failwith "lambda"

let rec lambdas xs alpha : hole E.m =
  match xs with
  | [] -> 
    E.ret alpha

  | x::xs ->
    lambda x alpha >>= 
    lambdas xs


let rec elab : type a. a ElabTm.t -> hole -> unit E.m =
  fun etm alpha ->
    match ElabTm.out etm with
    | ElabTm.Lam {vars; bdy} ->
      lambdas vars alpha >>=
      elab bdy
    | _ -> 
      failwith "TODO"