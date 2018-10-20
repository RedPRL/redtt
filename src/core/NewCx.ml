open RedBasis.Bwd

exception PleaseFillIn

module D = NewDomain
module Q = NewQuote

type t =
  {rel : NewRestriction.t;
   venv : D.Env.t;
   qenv : Q.QEnv.t;
   hyps : [`Dim | `Ty of D.con] bwd}

let rel cx = cx.rel
let genv cx = cx.venv.globals
let venv cx = cx.venv
let qenv cx = cx.qenv

let lookup cx ?(tw = `Only) ix =
  raise PleaseFillIn

(* make sure to unleash the [ushift] *)
let lookup_const cx ?(tw = `Only) ?(ushift = 0) x =
  raise PleaseFillIn

let extend _ ?name _ =
  raise PleaseFillIn

let extend_dim _ ?name =
  raise PleaseFillIn

let extend_dims _ ?names =
  raise PleaseFillIn

let restrict _ _ _ =
  raise PleaseFillIn

let restrict_ _ _ _ =
  raise PleaseFillIn
