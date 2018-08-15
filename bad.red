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
      | k=0 ⇒ λ z → p z
      | k=1 ⇒ λ z → p z
      ]
    in
    B (λ l → h l)
  in
  (coe 0 1 b in ty)

let thing1 (A : type) (a : A) : Path A a a =
  let bar =
  thing0 A
    (λ q → Path A (q 0) (q 1))
    (λ _ → a)
    (λ _ → a)

  in
  λ i -> bar i



let thing (A : type) (a,b : A) (p : Path A a b) : Path (Path A a b) p p =
  λ i j →
  let ty : dim → type = λ k →
    let h : dim → A = λ l →
      comp 0 l a [
      | k=0 ⇒ λ z → p z
      | k=1 ⇒ λ z → p z
      ]
    in
    Path (Path A (h 0) (h 1)) (λ l → h l) (λ l → h l)
  in
  (coe 0 1 (λ _ z → p z) in ty) i j

let experiment3 (A : type) (B : A -> type) (u : (a : A) -> B a) : Path ((a : A) -> B a) u u =
  lam i ->
    comp 0 1 u [
    | i=0 => lam j -> u
    | i=1 => lam j -> u
    ]



let experiment (A : type) (u : A)
  : (p : Path A u u) -> (q : Path (Path A u u) p p) -> Path (Path A u u) p p
  =
  lam p q i ->
    comp 0 1 (lam k -> p k) [
    | i=0 => lam j k -> q j k
    | i=1 => lam j k -> p k
    ]

; TODO: doesn't work yet, need elaborator support

;let experiment (A : type) (u : A) : Path A u u =
;  lam i ->
;    comp 0 1 ?cap [
;    | i=0 => lam j -> ?left
;    | i=1 => lam j -> ?right
;    ]


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
  | obase ⇒ lam _ -> obase
  | oloop (o' ⇒ compose/obase/r/o') i ⇒ lam j -> oloop (compose/obase/r/o' j) i
  ]
