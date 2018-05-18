type 'a tree =
  | Node of {label : 'a; children : 'a forest}

and 'a forest = 'a tree list

type 'a frame =
  {label : 'a;
   lefts : 'a forest;
   rights : 'a forest}

type 'a dtree =
  {below : 'a forest;
   above : 'a frame list}

type 'a zip = {label : 'a; ctx : 'a dtree}

let init label =
  let ctx = {below = []; above = []} in
  {label; ctx}

let cursor {label; _} =
  label

let insert lbl {label; ctx} =
  let node = Node {label = lbl; children = []} in
  let below = node :: ctx.below in
  let ctx' = {ctx with below} in
  {label; ctx = ctx'}

type move0 = [`Down | `Up | `Left | `Right]
type move = [`Id of move0 | `Star of move0]
exception InvalidMove of move0

let down {label; ctx} =
  match ctx.below with
  | [] ->
    raise @@ InvalidMove `Down

  | Node node :: xs ->
    let below = node.children in
    let frame = {label; lefts = []; rights = xs} in
    let above = frame :: ctx.above in
    let ctx' = {below; above} in
    {label = node.label; ctx = ctx'}

let up {label; ctx} =
  match ctx.above with
  | [] ->
    raise @@ InvalidMove `Up

  | frame :: above ->
    let node = Node {label; children = ctx.below} in
    let below = List.rev frame.lefts @ node :: frame.rights in
    let ctx' = {below; above} in
    {label = frame.label; ctx = ctx'}

let left {label; ctx} =
  match ctx.above with
  | [] ->
    raise @@ InvalidMove `Left

  | frame :: above ->
    match frame.lefts with
    | [] ->
      raise @@ InvalidMove `Left

    | Node x :: lefts ->
      let node = Node {label; children = ctx.below} in
      let frame' = {label = frame.label; lefts; rights = node :: frame.rights} in
      let ctx' = {below = x.children; above = frame' :: above} in
      {label = x.label; ctx = ctx'}

let right {label; ctx} =
  match ctx.above with
  | [] ->
    raise @@ InvalidMove `Right

  | frame :: above ->
    match frame.rights with
    | [] ->
      raise @@ InvalidMove `Right

    | Node x :: rights ->
      let node = Node {label; children = ctx.below} in
      let frame' = {label = frame.label; lefts = node :: frame.lefts; rights = rights} in
      let ctx' = {below = x.children; above = frame' :: above} in
      {label = x.label; ctx = ctx'}


let move0 m =
  match m with
  | `Down -> down
  | `Up -> up
  | `Left -> left
  | `Right -> right

let move m =
  match m with
  | `Id m0 ->
    move0 m0
  | `Star m0 ->
    let rec go zip =
      try go @@ move0 m0 zip with
      | _ -> zip
    in go
