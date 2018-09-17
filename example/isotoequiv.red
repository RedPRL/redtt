import equivalence

-- yacctt: https://github.com/mortberg/yacctt/blob/master/examples/prelude.ytt#L374
-- RedPRL: https://github.com/RedPRL/sml-redprl/blob/bd73932409ddc3479c8ded5ac32ae0d93d31874a/example/isotoequiv.prl
-- cubicaltt: https://github.com/mortberg/cubicaltt/blob/a331f1d355c5d2fc608a59c1cbbf016ea09d6deb/experiments/isoToEquiv.ctt

let iso (A B : type) : type =
  (f : A → B)
  × (g : B → A)
  × (α : (b : _) → path _ (f (g b)) b)
  × (a : _) → path _ (g (f a)) a

let iso/fiber/prop
  (A B : type)
  (I : iso A B) (b : B)
  : is-prop (fiber _ _ (I.fst) b)
  =
  let (f, g, α, β) = I in
  let sq (fib : fiber _ _ f b) (i j : dim) : A =
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


let iso→equiv (A B : type) (I : iso A B) : equiv A B =
  ( I.fst
  , λ b →
    ( (I.snd.fst b, I.snd.snd.fst b)
    , λ fib →
      iso/fiber/prop _ _ I b fib (I.snd.fst b, I.snd.snd.fst b)
    )
  )
