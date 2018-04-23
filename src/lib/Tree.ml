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

let down : 'a zip -> 'a zip = 
  fun {label; ctx} ->
    match ctx.below with 
    | [] -> 
      failwith "down: nothing below"

    | Node node :: xs -> 
      let below = node.children in
      let frame = {label; lefts = []; rights = xs} in
      let above = frame :: ctx.above in
      let ctx' = {below; above} in
      {label = node.label; ctx = ctx'}

let up : 'a zip -> 'a zip = 
  fun {label; ctx} ->
    match ctx.above with
    | [] ->
      failwith "up: nothing above"

    | frame :: above ->
      let node = Node {label; children = ctx.below} in
      let below = List.rev frame.lefts @ node :: frame.rights in
      let ctx' = {below; above} in
      {label = frame.label; ctx = ctx'}

let left : 'a zip -> 'a zip = 
  fun {label; ctx} ->
    match ctx.above with
    | [] ->
      failwith "left: nothing above"

    | frame :: above ->
      match frame.lefts with
      | [] ->
        failwith "left: nothing to the left"

      | Node x :: lefts ->
        let node = Node {label; children = ctx.below} in
        let frame' = {label = frame.label; lefts; rights = node :: frame.rights} in
        let ctx' = {below = x.children; above = frame' :: above} in
        {label = x.label; ctx = ctx'}

let right : 'a zip -> 'a zip = 
  fun {label; ctx} ->
    match ctx.above with
    | [] ->
      failwith "right: nothing above"

    | frame :: above ->
      match frame.rights with
      | [] ->
        failwith "right: nothing to the right"

      | Node x :: rights ->
        let node = Node {label; children = ctx.below} in
        let frame' = {label = frame.label; lefts = node :: frame.lefts; rights = rights} in
        let ctx' = {below = x.children; above = frame' :: above} in
        {label = x.label; ctx = ctx'}

type move = [`Down | `Up | `Left | `Right]

let move m =
  match m with
  | `Down -> down
  | `Up -> up
  | `Left -> left
  | `Right -> right