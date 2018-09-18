import equivalence

-- yacctt: https://github.com/mortberg/yacctt/blob/master/examples/prelude.ytt#L374
-- RedPRL: https://github.com/RedPRL/sml-redprl/blob/bd73932409ddc3479c8ded5ac32ae0d93d31874a/example/isotoequiv.prl
-- cubicaltt: https://github.com/mortberg/cubicaltt/blob/a331f1d355c5d2fc608a59c1cbbf016ea09d6deb/experiments/isoToEquiv.ctt

let iso (A B : type) : type =
  (f : A → B)
  × (g : B → A)
  × ((b : _) → path _ (f (g b)) b)
  × (a : _) → path _ (g (f a)) a

let iso/fiber/prop-over
  (A B : type)
  (I : iso A B) (b : dim → B)
  : is-prop-over (λ i → fiber _ _ (I.fst) (b i))
  =
  let (f, g, α, β) = I in
  let sq (b : B) (fib : fiber _ _ f b) (j k : dim) : A =
    comp k j (β (fib.fst) k) [
    | k=1 → refl
    | k=0 j → g (fib.snd j)
    ]
  in
  λ fib0 fib1 →
    let sq2 (i k : dim) : A =
      comp 0 k (g (b i)) [
      | i=0 → sq (b 0) fib0 1
      | i=1 → sq (b 1) fib1 1
      ]
    in
    λ i →
     ( refl
     , λ j →
        let aux : A =
          comp j 0 (β (sq2 i 1) j) [
          | j=1 → sq2 i
          | i=0 → sq (b 0) fib0 j
          | i=1 → sq (b 1) fib1 j
          ]
        in
        comp 0 1 (f aux) [
        | i=0 → α (fib0.snd j)
        | i=1 → α (fib1.snd j)
        | j=0 → α (f (sq2 i 1))
        | j=1 → α (b i)
        ]
     )

let iso→equiv (A B : type) (I : iso A B) : equiv A B =
  let (f, g, α, β) = I in
  (f , λ b → ((g b, α b), λ fib → iso/fiber/prop-over _ _ I (λ _ → b) fib (g b, α b)))

let iso→equiv-over (A B : type) (I : iso A B) : equiv-over A B =
  let (f, g, α, β) = I in
  (f , (λ b → (g b, α b), λ b fib → iso/fiber/prop-over _ _ I b fib (g (b 1), α (b 1))))
