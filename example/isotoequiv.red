import equivalence

; yacctt: https://github.com/mortberg/yacctt/blob/master/examples/prelude.ytt#L374
; RedPRL: https://github.com/RedPRL/sml-redprl/blob/bd73932409ddc3479c8ded5ac32ae0d93d31874a/example/isotoequiv.prl
; cubicaltt: https://github.com/mortberg/cubicaltt/blob/a331f1d355c5d2fc608a59c1cbbf016ea09d6deb/experiments/isoToEquiv.ctt

let Iso (A B : type) : type =
  (f : A → B)
  × (g : B → A)
  × (α : (b : _) → Path _ (f (g b)) b)
  × (a : _) → Path _ (g (f a)) a

let Iso/fiber-is-prop
  (A B : type)
  (I : Iso A B) (b : B)
  : IsProp (Fiber _ _ (I.fst) b)
  =
  let f = I.fst in
  let g = I.snd.fst in
  let α = I.snd.snd.fst in
  let β = I.snd.snd.snd in

  let sq (fib : Fiber _ _ (I.fst) b) (i j : dim) : A =
    comp 0 j (g (fib.snd i)) [
    | i=0 → β (fib.fst)
    | i=1 → refl
    ]
  in
  λ fib0 fib1 →
    let sq2 (i j : dim) : A =
      comp 1 j (g b) [
      | i=0 k → sq fib0 k 1
      | i=1 k → sq fib1 k 1
      ]
    in
    λ i →
     ( refl
     , λ j →
        let aux : A =
          comp 1 0 (sq2 i j) [
          | i=0 → sq fib0 j
          | i=1 → sq fib1 j
          | j=0 → β (sq2 i 0)
          | j=1 → refl
          ]
        in
        comp 0 1 (f aux) [
        | i=0 → α (fib0.snd j)
        | i=1 → α (fib1.snd j)
        | j=0 → α (f (sq2 i 0))
        | j=1 → α b
        ]
     )


let Iso/Equiv (A B : type) (I : Iso A B) : Equiv A B =
  ( I.fst
  , λ b →
    ( (I.snd.fst b, I.snd.snd.fst b)
    , λ fib →
      Iso/fiber-is-prop _ _ I b fib (I.snd.fst b, I.snd.snd.fst b)
    )
  )
