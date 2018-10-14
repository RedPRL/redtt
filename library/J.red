import path

def J (A : type) (p : 𝕀 → A) (C : [i] A [i=0 → p 0] → type) (d : C refl) : C p =
  coe 0 1 d in λ i →
    C (λ j → comp 0 j (p 0) [i=0 → refl | i=1 → p])

def J/eq
  (A : type) (a : A)
  (C : [i] A [i=0 → a] → type) (d : C refl)
  : path (C refl) (J _ (λ _ → a) C d) d
  =
  let square (i j : 𝕀) : A = comp 0 j a [∂[i] → refl] in
  λ k →
    let mot (i : 𝕀) = C (λ j → comp 0 j a [k=0 → square i | k=1 | ∂[i] → refl]) in
    comp 0 1 d in mot [
    | k=0 → λ i → coe 0 i d in λ j → C (square j)
    | k=1 → refl
    ]
