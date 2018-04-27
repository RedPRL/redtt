type tm = Tm.chk Tm.t
type dim = DimVal.t
type query = Eq of dim * dim

type can = [`Can]
type neu = [`Can]

type _ cmd =
  | Ask : query -> DimVal.compare cmd
  | Fresh : Symbol.t cmd
  | Ret : 'a -> 'a cmd
  | Bind : ('a -> 'b cmd) * 'a cmd -> 'b cmd
  | Restrict : dim * dim * 'a cmd -> 'a cmd

and _ val_ =
  | Pi : {dom : can val_ cmd; cod : clo cmd} -> can val_
  | V : {dim : dim; ty0 : can val_ cmd; ty1 : can val_ cmd; equiv : can val_ cmd} -> can val_
  | VIn : dim * can val_ * can val_ -> can val_

  | Coe : {dim0 : dim; dim1 : dim; ty : Symbol.t * can val_; el : can val_} -> can val_

  | Lam : clo -> can val_
  | Pair : can val_ * can val_ -> can val_
  | FunApp : neu val_ * can val_ -> can val_
  | ExtApp : neu val_ * dim -> can val_

and clo = tm * env
and env = can val_ list

let ret v =
  Ret v

let (>>=) m k =
  Bind (k, m)

let ask dim0 dim1 =
  Ask (Eq (dim0, dim1))

let (<&>) m1 m2 =
  m1 >>= fun x1 ->
  m2 >>= fun x2 ->
  ret (x1, x2)

module D = DimVal

let restrict (x, y) m =
  Restrict (x, y, m)

let car : can val_ -> can val_ cmd = failwith ""
let cdr : can val_ -> can val_ cmd  = failwith ""

let apply : can val_ -> can val_ -> can val_ cmd = failwith ""

let rec coe r r' (x, ty) el =
  match ty with
  | V vinfo ->
    begin
      ask vinfo.dim (D.Fresh x) <&> ask r DimVal.Dim1 >>= function
      | D.Same, D.Same ->
        restrict (r', D.Fresh x) vinfo.equiv >>= fun equiv_r' ->
        vinfo.ty1 >>= fun tyb ->
        coe D.Dim1 r' (x, tyb) el >>= fun coe1r'bn ->
        cdr equiv_r' >>= fun cdr_equiv_r' ->
        apply cdr_equiv_r' coe1r'bn >>= fun app_cdr_equiv ->
        car app_cdr_equiv >>= fun otm ->
        car otm >>= fun otm0 ->
        ret @@ VIn (r', otm0, failwith "TODO")

      | _ -> failwith "TODO"
    end

  | _ ->
    failwith "TODO"
