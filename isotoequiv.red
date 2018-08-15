import equivalence

; yacctt: https://github.com/mortberg/yacctt/blob/master/examples/prelude.ytt#L374
; RedPRL: https://github.com/RedPRL/sml-redprl/blob/bd73932409ddc3479c8ded5ac32ae0d93d31874a/example/isotoequiv.prl
; cubicaltt: https://github.com/mortberg/cubicaltt/blob/a331f1d355c5d2fc608a59c1cbbf016ea09d6deb/experiments/isoToEquiv.ctt

let Iso (A, B : type) : type =
  (f : A → B)
  × (g : B → A)
  × (α : (b : _) → Path _ (f (g b)) b)
  × (a : _) → Path _ (g (f a)) a

let Iso/fiber-is-prop
  (A, B : type)
  (I : Iso A B) (b : B)
  : IsProp (Fiber _ _ (I.0) b)
  =
  let f = I.0 in
  let g = I.1.0 in
  let α = I.1.1.0 in
  let β = I.1.1.1 in

  let sq : (_ : Fiber _ _ (I.0) b) (i, j : dim) → A =
    λ fib i j →
      comp 0 j (g (fib.1 i)) [
      | i=0 ⇒ β (fib.0)
      | i=1 ⇒ auto
      ]
  in
  λ fib0 fib1 →
    let sq2 : (i, j : dim) → A =
      λ i j →
        comp 1 j (g b) [
        | i=0 ⇒ λ k → sq fib0 k 1
        | i=1 ⇒ λ k → sq fib1 k 1
        ]
    in
    λ i →
     < sq2 i 0
     , λ j →
        let aux : A =
          comp 1 0 (sq2 i j) [
          | i=0 ⇒ sq fib0 j
          | i=1 ⇒ sq fib1 j
          | j=0 ⇒ β (sq2 i 0)
          | j=1 ⇒ auto
          ]
        in
        comp 0 1 (f aux) [
        | i=0 ⇒ α (fib0.1 j)
        | i=1 ⇒ α (fib1.1 j)
        | j=0 ⇒ α (f (sq2 i 0))
        | j=1 ⇒ α b
        ]
     >


let Iso/Equiv (A, B : type) (I : Iso A B) : Equiv A B =
  < I.0
  , λ b →
    < <I.1.0 b, I.1.1.0 b>
    , λ fib →
      Iso/fiber-is-prop _ _ I b fib <I.1.0 b, I.1.1.0 b>
    >
  >
