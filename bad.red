import path

; Here are some tricky examples that Evan Cavallo came up with to expose bugs.

data O where
| obase
| oloop (y : O) @ i
  [ i=0 ⇒ y
  | i=1 ⇒ y
  ]

let thing0 (A : type) (B : (dim → A) → type) (p : dim → A) (b : B p) : B p =
  let ty : dim → type = λ k →
    let h : dim → A = λ l →
      comp 0 l (p 0) [
      | k=0 ⇒ p
      | k=1 ⇒ p
      ]
    in
    B h
  in
  (coe 0 1 b in ty)

let thing1 (A : type) (a : A) : Path A a a =
  thing0 A
    (λ q → Path A (q 0) (q 1))
    (λ _ → a)
    auto



let thing (A : type) (a,b : A) (p : Path A a b) : Path (Path A a b) p p =
  λ i j →
  let ty : dim → type = λ k →
    let h : dim → A = λ l →
      comp 0 l a [
      | k=0 ⇒ p
      | k=1 ⇒ p
      ]
    in
    Path (Path A (h 0) (h 1)) h h
  in
  (coe 0 1 (λ _ → p) in ty) i j

let experiment3 (A : type) (B : A -> type) (u : (a : A) -> B a) : Path ((a : A) -> B a) u u =
  λ i ->
    comp 0 1 u [
    | i=0 => auto
    | i=1 => auto
    ]



let experiment (A : type) (u : A)
  : (p : Path A u u) -> (q : Path (Path A u u) p p) -> Path (Path A u u) p p
  =
  λ p q i ->
    comp 0 1 p [
    | i=0 => q
    | i=1 => auto
    ]

; Note to Evan: your example with the holes was not supposed to work after all.
; You can surround the partially-defined composition with a question ?{ ... };
; what this is deactivate the ambient restriction long enough for you to build
; a term which satisfies it. This is useful for intermediate states that don't yet
; satisfy the restriction. Once your term checks, then delete the ?{ ... }.
;
;;let experiment (A : type) (u : A) : Path A u u =
;;  λ i ->
;;  ?{
;;    comp 0 1 ?cap [
;;    | i=0 => λ j -> ?left
;;    | i=1 => λ j -> ?right
;;    ]
;;  }
;;

let id (o : O) : O =
  elim o [
  | obase ⇒ obase
  | oloop (o' ⇒ id/o') i ⇒ oloop id/o' i
  ]

data void where

data T where
| tbase [u : void]
| tloop [u : void] @ i
  [ i=0 ⇒ tbase u
  | i=1 ⇒ tbase u
  ]

let compose (o1,o2 : O) : O =
  elim o1 [
  | obase ⇒ o2
  | oloop (o1' ⇒ compose/o1'/o2) i ⇒ oloop compose/o1'/o2 i
  ]

let compose/obase/r (o : O) : Path O (compose o obase) o =
  elim o [
  | obase ⇒ auto
  | oloop (o' ⇒ compose/obase/r/o') i ⇒ λ j -> oloop (compose/obase/r/o' j) i
  ]





data unit where
| triv

data twonit where
| wrap [x : unit]

let Code (n : twonit) : type =
  elim n [ wrap n' => dim -> unit ]

let test (p : Path twonit (wrap triv) (wrap triv)) : dim -> unit =
  coe 0 1 (λ _ -> triv) in (λ i -> Code (p i))




