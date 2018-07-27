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
  (A : type) (B : type)
  (I : Iso A B) (b : B)
  : IsProp (Fiber _ _ (I.0) b)
  =
  let f = I.0 in
  let g = I.1.0 in
  let α = I.1.1.0 in
  let β = I.1.1.1 in

  let sq : (_ : Fiber _ _ (I.0) b) (i, j : dim) → A =
    λ fib i j →
      comp 0 j (g (fib.1 i)) with
      | i=0 ⇒ λ k → β (fib.0) k
      | i=1 ⇒ λ _ → g b
      end
  in
  λ fib0 fib1 →
    let sq2 : (i, j : dim) → A =
      λ i j →
        comp 1 j (g b) with
        | i=0 ⇒ λ k → sq fib0 k 1
        | i=1 ⇒ λ k → sq fib1 k 1
        end
    in
    λ i →
     < sq2 i 0
     , λ j →
        let aux : A =
          comp 1 0 (sq2 i j) with
          | i=0 ⇒ λ k → sq fib0 j k
          | i=1 ⇒ λ k → sq fib1 j k
          | j=0 ⇒ λ k → β (sq2 i 0) k
          | j=1 ⇒ λ _ → g b
          end
        in
        comp 0 1 (f aux) with
        | i=0 ⇒ λ k → α (fib0.1 j) k
        | i=1 ⇒ λ k → α (fib1.1 j) k
        | j=0 ⇒ λ k → α (f (sq2 i 0)) k
        | j=1 ⇒ λ k → α b k
        end
     >


let Iso/Equiv (A, B : type) (I : Iso A B) : Equiv A B =
  < I.0
  , λ b →
    < <I.1.0 b, I.1.1.0 b>
    , λ fib →
      Iso/fiber-is-prop _ _ I b fib <I.1.0 b, I.1.1.0 b>
    >
  >
