type name = string

type 'a f =
  | Atom of string
  | Numeral of int
  | List of 'a list
  | TyBind of name * 'a * 'a
  | Tube of 'a * 'a * 'a
  | Bind of name * 'a

type info = Lexing.position * Lexing.position
type t = Node of {info : info; con : t f}

type tybind_hole = [`Ty | `Bdy]
type tube_hole = [`Dim0 | `Dim1 | `Bdy]

type 'a frame = 
  | KList of info * 'a list * 'a list
  | KBind of info * string
  | KTyBind of info * string * tybind_hole * 'a
  | KTube of info * tube_hole * 'a * 'a

module type ResEnv =
sig
  type t
  val init : t
  val bind : string -> t -> t
  val get : string -> t -> Thin.t
end

module ResEnv : ResEnv = 
struct
  type t = string list

  let init = []
  let bind x env = x :: env
  let rec get x env =
    match env with 
    | [] ->
      failwith "variable not found"
    | y :: ys ->
      if x = y 
      then Thin.id
      else Thin.skip @@ get x ys
end

module ReaderCombinators :
sig
  type node = t
  type 'a m

  val run : 'a m -> node -> 'a

  val ret : 'a -> 'a m
  val (>>=) : 'a m -> ('a -> 'b m) -> 'b m
  val (>>) : 'a m -> 'b m -> 'b m
  val (<|>) : 'a m -> 'a m -> 'a m
  val (<+>) : 'a m -> 'b m -> [`L of 'a | `R of 'b] m
  val (<$>) : ('a -> 'b) -> 'a m -> 'b m
  val fix : ('a m -> 'a m) -> 'a m
  val fix2 : ('a m * 'b m -> 'a m) -> ('a m * 'b m -> 'b m) -> 'a m * 'b m

  val error : string -> 'a m

  val num : int m
  val atom : string m
  val kwd : string -> unit m

  val var : Thin.t m

  val peek_info : info m
  val open_list : 'a m -> 'a m
  val open_bind : 'a m -> 'a m
  val open_tybind : 'a m -> 'a m
  val open_tube : 'a m -> 'a m

  val right : unit m
  val left : unit m

  val many1 : 'a m -> 'a list m
  val many : 'a m -> 'a list m
end = 
struct
  type node = t
  type env = ResEnv.t
  type stack = (env * node frame) list

  exception Error of {msg : string; info : info}

  type state = {head : node; env : ResEnv.t; stack : stack}
  type 'a m = state -> 'a * state

  let run (m : 'a m) node : 'a =
    let a, _ = m {head = node; env = ResEnv.init; stack = []} in
    a


  let ret x state = 
    x, state

  let (>>=) (m : 'a m) (k : 'a -> 'b m) : 'b m =
    fun state ->
      let a, state' = m state in
      k a state'

  let (<$>) f m =
    m >>= fun x ->
    ret @@ f x

  let (>>) m n = 
    m >>= fun _ ->
    n

  let (<|>) m1 m2 state =
    try 
      m1 state
    with _ -> 
      m2 state

  let (<+>) m1 m2 : [`L of 'a | `R of 'b] m =
    fun state ->
      try 
        ((fun x -> `L x) <$> m1) state
      with _ -> 
        ((fun x -> `R x) <$> m2) state

  let rec fix f state =
    f (fix f) state

  let rec fix2 f g =
    (fun state -> f (fix2 f g) state), 
    (fun state -> g (fix2 f g) state)

  let peek_info {head = Node {info} as node; env; stack} =
    info, {head = node; env; stack}

  let peek_env {head; env; stack} = 
    env, {head; env; stack}

  let error msg =
    peek_info >>= fun info ->
    (fun _ ->
       raise @@ Error {msg; info})

  let atom : string m =
    fun state ->
      let Node node = state.head in
      match node.con with
      | Atom nm -> 
        nm, state
      | _ -> 
        raise @@ Error {msg = "Expected atom"; info = node.info}


  let var : Thin.t m = 
    atom >>= fun nm ->
    peek_env >>= fun env ->
    match ResEnv.get nm env with
    | th -> 
      ret th
    | exception _ -> 
      error "Could not resolve variable"


  let num : int m =
    fun state ->
      let Node node = state.head in
      match node.con with
      | Numeral i -> 
        i, state
      | _ -> 
        raise @@ Error {msg = "Expected numeral"; info = node.info}

  let kwd : string -> unit m =
    fun nm ->
      atom >>= fun nm' ->
      if nm = nm' then ret () else
        error "Keyword mismatch"

  let down_list : unit m =
    fun state ->
      let Node node = state.head in
      match node.con with
      | List (x :: xs) ->
        (), {head = x; stack = (state.env, KList (node.info, [], xs)) :: state.stack; env = state.env}

      | _ ->
        raise @@ Error {msg = "Expected list"; info = node.info}

  let down_tube : unit m = 
    fun state ->
      let Node node = state.head in
      match node.con with
      | Tube (dim0, dim1, bdy) ->
        (), {head = dim0; stack = (state.env, KTube (node.info, `Dim0, dim1, bdy)) :: state.stack; env = state.env}

      | _ ->
        raise @@ Error {msg = "Expectd tube"; info = node.info}

  let down_bind : string m =
    fun state ->
      let Node node = state.head in
      match node.con with
      | Bind (nm, x) ->
        let env = ResEnv.bind nm state.env in
        nm, {head = x; stack = (state.env, KBind (node.info, nm)) :: state.stack; env}

      | _ ->
        raise @@ Error {msg = "Expected binder"; info = node.info}

  let down_tybind : string m = 
    fun state ->
      let Node node = state.head in
      match node.con with
      | TyBind (nm, ty, bdy) ->
        nm, {head = ty; stack = (state.env, KTyBind (node.info, nm, `Ty, bdy)) :: state.stack; env = state.env}

      | _ ->
        raise @@ Error {msg = "Expected typed binder"; info = node.info}

  let up : unit m = 
    fun state ->
      match state.stack with
      | [] ->
        let Node {info} = state.head in
        raise @@ Error {msg = "Cannot go up"; info}

      | (env, KList (info, xs, ys)) :: stk ->
        let con = List (List.rev xs @ state.head :: ys) in
        (), {head = Node {info; con}; stack = stk; env}

      | (env, KBind (info, nm)) :: stk ->
        let con = Bind (nm, state.head) in
        (), {head = Node {info; con}; stack = stk; env}

      | (env, KTyBind (info, nm, `Ty, bdy)) :: stk ->
        let con = TyBind (nm, state.head, bdy) in
        (), {head = Node {info; con}; stack = stk; env}

      | (env, KTyBind (info, nm, `Bdy, ty)) :: stk ->
        let con = TyBind (nm, ty, state.head) in
        (), {head = Node {info; con}; stack = stk; env}

      | (env, KTube (info, `Dim0, dim1, bdy)) :: stk ->
        let con = Tube (state.head, dim1, bdy) in
        (), {head = Node {info; con}; stack = stk; env}

      | (env, KTube (info, `Dim1, dim0, bdy)) :: stk ->
        let con = Tube (dim0, state.head, bdy) in
        (), {head = Node {info; con}; stack = stk; env}

      | (env, KTube (info, `Bdy, dim0, dim1)) :: stk ->
        let con = Tube (dim0, dim1, state.head) in
        (), {head = Node {info; con}; stack = stk; env}


  let left : unit m = 
    fun state ->
      match state.stack with
      | (env', KList (info, x::xs, ys)) :: stk ->
        (), {head = x; stack = (env', KList (info, xs, state.head :: ys)) :: stk; env = state.env}

      | (env', KTyBind (info, nm, `Bdy, ty)) :: stk ->
        (), {head = ty; stack = (env', KTyBind (info, nm, `Bdy, state.head)) :: stk; env = env'}

      | _ ->
        let Node {info} = state.head in
        raise @@ Error {msg = "Cannot go left"; info}

  let right : unit m =
    fun state ->
      match state.stack with
      | (env', KList (info, xs, y :: ys)) :: stk ->
        (), {head = y; stack = (env', KList (info, state.head :: xs, ys)) :: stk; env = state.env}

      | (env', KTyBind (info, nm, `Ty, bdy)) :: stk ->
        let env'' = ResEnv.bind nm state.env in
        (), {head = bdy; stack = (env', KTyBind (info, nm, `Bdy, state.head)) :: stk; env = env''}

      | _ ->
        let Node {info} = state.head in
        raise @@ Error {msg = "Cannot go right"; info}

  let open_list (m : 'a m) : 'a m =
    down_list >> m >>= fun x -> up >> ret x

  let open_bind (m : 'a m) : 'a m =
    down_bind >> m >>= fun x -> up >> ret x

  let open_tybind (m : 'a m) : 'a m =
    down_tybind >> m >>= fun x -> up >> ret x

  let open_tube (m : 'a m) : 'a m =
    down_tube >> m >>= fun x -> up >> ret x


  let many1 m = 
    fix @@ fun k -> 
    m >>= fun x ->
    right >>
    (k <|> ret []) >>= fun xs ->
    ret @@ x :: xs

  let many m =
    many1 m <|> ret []


end

module Reader :
sig
  type 'a m = 'a ReaderCombinators.m

  val chk : Tm.chk Tm.t m
  val inf : Tm.inf Tm.t m
end = 
struct
  type _ tag = 
    | Chk : Tm.chk tag
    | Inf : Tm.inf tag

  module R = ReaderCombinators
  type 'a m = 'a R.m

  let (>>=) = R.(>>=)
  let (>>) = R.(>>)
  let (<|>) = R.(<|>)
  let (<+>) = R.(<+>)
  let (<$>) = R.(<$>)

  let lambda chk =
    R.peek_info >>= fun info ->
    R.open_list @@ 
    R.kwd "lam" >>
    R.right >>
    R.fix @@ fun kont ->
    R.open_bind @@ 
    (kont <|> chk) >>= fun tm ->
    R.ret @@ Tm.into_info info @@ Tm.Lam (Tm.B tm)

  let pi chk =
    R.peek_info >>= fun info ->
    R.open_list @@
    R.kwd "->" >>
    R.fix @@ fun kont ->
    R.open_tybind @@
    chk >>= fun dom ->
    R.right >>
    (kont <|> chk) >>= fun cod ->
    R.ret @@ Tm.into_info info @@ Tm.Pi (dom, Tm.B cod)

  let sg chk =
    R.peek_info >>= fun info ->
    R.open_list @@
    R.kwd "*" >>
    R.fix @@ fun kont ->
    R.open_tybind @@
    chk >>= fun dom ->
    R.right >>
    (kont <|> chk) >>= fun cod ->
    R.ret @@ Tm.into_info info @@ Tm.Sg (dom, Tm.B cod)


  let tube chk = 
    R.open_tube @@
    chk >>= fun dim0 ->
    R.right >>
    chk >>= fun dim1 ->
    R.right >>
    chk >>= fun bdy ->
    R.ret @@ (dim0, dim1, Some bdy)

  let btube chk = 
    R.open_tube @@
    chk >>= fun dim0 ->
    R.right >>
    chk >>= fun dim1 ->
    R.right >>
    (R.open_bind chk) >>= fun bdy ->
    R.ret @@ (dim0, dim1, Some (Tm.B bdy))

  let ext chk =
    R.peek_info >>= fun info ->
    R.open_list @@
    R.kwd "#" >>
    R.right >>
    R.open_bind @@
    R.open_list @@
    chk >>= fun cod ->
    R.many1 (tube chk) >>= fun sys ->
    R.ret @@ Tm.into_info info @@ Tm.Ext (Tm.B (cod, sys))

  let empty_ext chk =
    R.peek_info >>= fun info ->
    R.open_list @@
    R.kwd "#" >>
    R.right >>
    R.open_bind @@
    chk >>= fun cod ->
    R.ret @@ Tm.into_info info @@ Tm.Ext (Tm.B (cod, []))

  let univ =
    R.peek_info >>= fun info ->
    R.open_list @@
    R.kwd "U" >>
    R.right >>
    R.num >>= fun i ->
    R.ret @@ Tm.into_info info @@ Tm.Univ (Lvl.Const i)

  let bool =
    R.peek_info >>= fun info ->
    R.kwd "bool" >>
    R.ret @@ Tm.into_info info @@ Tm.Bool

  let up inf =
    R.peek_info >>= fun info ->
    inf >>= fun tm ->
    R.ret @@ Tm.into_info info @@ Tm.Up tm

  let down chk = 
    R.peek_info >>= fun info ->
    R.open_list @@
    R.kwd ":>" >>
    R.right >>
    chk >>= fun ty ->
    R.right >>
    chk >>= fun tm ->
    R.ret @@ Tm.into_info info @@ Tm.Down {ty; tm}

  let coe chk = 
    R.peek_info >>= fun info ->
    R.open_list @@
    R.kwd "coe" >>
    R.right >>
    chk >>= fun dim0 ->
    R.right >>
    chk >>= fun dim1 ->
    R.right >>
    (R.open_bind chk) >>= fun ty ->
    R.right >>
    chk >>= fun tm ->
    R.ret @@ Tm.into_info info @@ Tm.Coe {dim0; dim1; ty = Tm.B ty; tm}

  let hcom chk =
    R.peek_info >>= fun info ->
    R.open_list @@ 
    R.kwd "hcom" >>
    R.right >>
    chk >>= fun dim0 ->
    R.right >>
    chk >>= fun dim1 ->
    R.right >>
    chk >>= fun ty ->
    R.right >>
    chk >>= fun cap ->
    R.right >>
    R.many1 (btube chk) >>= fun sys ->
    R.ret @@ Tm.into_info info @@ Tm.HCom {dim0; dim1; ty; cap; sys}

  let com chk =
    R.peek_info >>= fun info ->
    R.open_list @@ 
    R.kwd "com" >>
    R.right >>
    chk >>= fun dim0 ->
    R.right >>
    chk >>= fun dim1 ->
    R.right >>
    (R.open_bind chk) >>= fun ty ->
    R.right >>
    chk >>= fun cap ->
    R.right >>
    R.many1 (btube chk) >>= fun sys ->
    R.ret @@ Tm.into_info info @@ Tm.Com {dim0; dim1; ty = Tm.B ty; cap; sys}

  let var =
    R.peek_info >>= fun info ->
    R.var >>= fun th ->
    R.ret @@ Tm.into_info info @@ Tm.Var th

  let fun_app inf chk =
    R.peek_info >>= fun info ->
    R.open_list @@
    inf >>= fun fn ->
    R.right >>
    chk >>= fun arg0 ->
    R.right >>
    R.many chk >>= fun rest ->
      let app0 = Tm.into_info info @@ Tm.FunApp (fn, arg0) in
      R.ret @@ List.fold_right (fun arg app -> Tm.into_info info @@ Tm.FunApp (app, arg)) rest app0

  let ext_app inf chk =
    R.peek_info >>= fun info ->
    R.open_list @@
    R.kwd "@" >>
    R.right >>
    inf >>= fun fn ->
    R.right >>
    chk >>= fun arg0 ->
    R.right >>
    R.many chk >>= fun rest ->
      let app0 = Tm.into_info info @@ Tm.FunApp (fn, arg0) in
      R.ret @@ List.fold_right (fun arg app -> Tm.into_info info @@ Tm.FunApp (app, arg)) rest app0


  let chk_f (chk, inf) =
    lambda chk <|>
    pi chk <|>
    sg chk <|>
    ext chk <|>
    empty_ext chk <|>
    bool <|>
    univ <|>
    up inf

  let inf_f (chk, inf) =
    coe chk <|>
    hcom chk <|>
    com chk <|>
    var <|>
    down chk

  let chk, inf = 
    R.fix2 chk_f inf_f

end