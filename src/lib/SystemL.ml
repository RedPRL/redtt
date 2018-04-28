module SystemL =
struct
  type dim = DimVal.t
  type rel = DimRel.t

  type can =
    | VLam of tm

  and tm =
    | Fn of (tm -> tm)
    | Mu of (rel -> stk -> cmd)
    | Nil
    | Cons of tm * tm
    | Ret of can

  and stk =
    | StkE
    | StkApp of tm * stk
    | StkRestrict of rel * stk
    | StkProj of int * stk

  and cotm =
    | MuTilde of (tm -> cmd)
    | Stk of stk

  and cmd =
    | Cut of tm * cotm

  let (||) t e =
    Cut (t, e)

  let mu c = Mu c

  let ret v = Ret v

  let get_rel t =
    mu @@ fun rel alpha ->
    Cut (t rel, Stk alpha)

  let stk pi = Stk pi

  let kapp u pi = StkApp (u, pi)

  let app t u =
    mu @@ fun _ alpha ->
    Cut (t, stk @@ kapp u alpha)

  let fn t = Fn t

  let restrict rel t =
    mu @@ fun _ alpha ->
    Cut (t, stk @@ StkRestrict (rel, alpha))

  let cons t u =
    Cons (t, u)

  let vlam t = VLam t

  let rec exec rel cmd =
    let Cut (t, e) = cmd in
    cut rel t e

  and cut rel t e =
    match e with
    | Stk pi ->
      lfoc rel t pi

    | MuTilde c ->
      exec rel @@ c t

  and lfoc rel t pi =
    match t, pi with
    | Fn t, StkApp (v, pi) ->
      lfoc rel (t v) pi

    | Mu c, pi ->
      exec rel @@ c rel pi

    | _, StkRestrict (rel', pi) ->
      lfoc rel' t pi

    | Cons (t, _), StkProj (0, pi) ->
      lfoc rel t pi

    | Cons (_, u), StkProj (n, pi) ->
      lfoc rel u @@ StkProj (n - 1, pi)

    | _, StkE ->
      t

    | _ ->
      failwith "lfoc"



  let compare d0 d1 t =
    mu @@ fun rel alpha ->
    let t' = t @@ DimRel.compare_dim rel d0 d1 in
    t' || stk alpha

  (*
    Example:

    I am writing φ for restrictions and α for stacks.

    let's write μφ => t for μ<φ,α> => <t φ || α>

    [| (lam M) |] ==
      λρ => μφ =>
      vlam (λv. restrict φ in {[| M |] (v::ρ)})
     *)

   (*
     [| (V r A B E) |] ==
       λρ => μφ =>
         let r = [| r |] ρ in
         let A = (λ- => μψ => restrict (φ/\ψ) in [| A |] ρ) in
         let B = (λ- => μψ => restrict (φ/\ψ) in [| B |] ρ) in
         let E = (λ- => μψ => restrict (φ/\ψ) in [| E |] ρ) in
         vv r A B E


    What is going on in the above is that we are giving anyone who is reading the 'vv' value the opportunity to
    impose a restriction A or B or E (this corresponds to substitution in the operational semantics).

    The way that would work is that I would write something like:

        μφ =>
          let A<r'/x> = (restrict (φ; r' = x) in A()) in
          ...

    What this does is: find the current restriction, and execute the thunk A under the current restriction extended by r'=x *and*
    by the restriction that was installed when the V type was first evaluated. This is analogous to how when we form a closure,
    we must snapshot the current environment.
    *)



  let rec eval : type a. Tm.chk Tm.t -> tm =
    fun tm ->
      match Tm.out tm with
      | Tm.Lam (Tm.B (_, bdy)) ->
        fn @@ fun env ->
        mu @@ fun rel alpha ->
        let clo =
          ret @@ vlam @@ fn @@ fun v ->
          restrict rel @@
          app (eval bdy) @@
          cons v env
        in
        clo || stk alpha

      | _ ->
        failwith ""

end
