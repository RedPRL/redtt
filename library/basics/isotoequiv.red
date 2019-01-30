import prelude

-- yacctt: https://github.com/mortberg/yacctt/blob/master/examples/prelude.ytt#L374
-- RedPRL: https://github.com/RedPRL/sml-redprl/blob/bd73932409ddc3479c8ded5ac32ae0d93d31874a/example/isotoequiv.prl
-- cubicaltt: https://github.com/mortberg/cubicaltt/blob/a331f1d355c5d2fc608a59c1cbbf016ea09d6deb/experiments/isoToEquiv.ctt

def iso (A B : type) : type =
  (f : A → B)
  × (g : B → A)
  × ((b : _) → path _ (f (g b)) b)
  × (a : _) → path _ (g (f a)) a

def iso/refl (A : type) : iso A A = 
  ( λ f → f
  , λ g → g
  , λ _ → refl
  , λ _ → refl
  )

def iso/symm (A B : type) (I : iso A B) : iso B A =
  let (f,g,α,β) = I in (g,f,β,α)

def iso/trans (A B C : type) (I1 : iso A B) (I2 : iso B C) : iso A C = 
  let (f1,g1,α1,β1) = I1 in
  let (f2,g2,α2,β2) = I2 in
  ( λ a → f2 (f1 a)
  , λ c → g1 (g2 c)
  , λ c → trans _ (λ j → f2 (α1 (g2 c) j)) (α2 c)
  , λ a → trans _ (λ j → g1 (β2 (f1 a) j)) (β1 a)
  )  

def iso/fiber/prop-over
  (A B : type)
  (I : iso A B) (b : 𝕀 → B)
  : is-prop-over (λ i → fiber _ _ (I.fst) (b i))
  =
  let (f, g, α, β) = I in
  let sq (b : B) (fib : fiber _ _ f b) (j k : 𝕀) : A =
    comp k j (β (fib.fst) k) [
    | k=1 → refl
    | k=0 j → g (fib.snd j)
    ]
  in
  λ fib0 fib1 →
  let sq2 (i k : 𝕀) : A =
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

def iso→equiv (A B : type) (I : iso A B) : equiv A B =
  let (f, g, α, β) = I in
  (f , λ b → ((g b, α b), λ fib → iso/fiber/prop-over _ _ I (λ _ → b) fib (g b, α b)))

/-
def iso→equiv-over (A B : type) (I : iso A B) : equiv-over A B =
  let (f, g, α, β) = I in
  (f , (λ b → (g b, α b), λ b fib → iso/fiber/prop-over _ _ I b fib (g (b 1), α (b 1))))
-/

def equiv→iso (A B : type) (e : equiv A B) : iso A B =
  ( e .fst
  , λ b → e .snd b .fst .fst
  , λ b → e .snd b .fst .snd
  , λ a i → symm (fiber A B (e .fst) (e .fst a)) (e .snd (e .fst a) .snd (a, refl)) i .fst
  )
