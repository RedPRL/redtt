import path

def J
  (A : type) (a : A)
  (C : ([i] A [i=0 → a]) → type)
  (d : C refl)
  (p : [i] A [i=0 → a])
  : C p
  =
  coe 0 1 d in λ i →
    C (λ j → comp 0 j a [i=0 → refl | i=1 → p])

def J/eq
  (A : type) (a : A)
  (C : ([i] A [i=0 → a]) → type) (d : C refl)
  : path (C refl) (J _ _ C d refl) d
  =
  let square (i j : 𝕀) : A = comp 0 j a [∂[i] → refl] in
  λ k →
    let mot (i : 𝕀) = C (λ j → comp 0 j a [k=0 → square i | k=1 | ∂[i] → refl]) in
    comp 0 1 d in mot [
    | k=0 → λ i → coe 0 i d in λ j → C (square j)
    | k=1 → refl
    ]
