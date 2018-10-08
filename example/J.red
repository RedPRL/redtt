import path

def J
  (A : type) (a : A)
  (C : (x : A) (p : path _ a x) → type) (d : C a refl)
  (x : A) (p : path _ a x)
  : C x p
  =
  coe 0 1 d in λ i →
    let h (j : dim) : A = comp 0 j a [i=0 → refl | i=1 → p] in
    C (h 1) h

def J/eq
  (A : type) (a : A)
  (C : (x : A) (p : path A a x) → type) (d : C a refl)
  : path (C a refl) (J _ _ C d a refl) d
  =
  let square (i j : dim) : A = comp 0 j a [∂[i] → refl] in
  λ k →
    comp 0 1 d in λ i →
      let aux (j : dim) : A =
        comp 0 j a [
        | k=0 → square i
        | k=1 | ∂[i] → refl
        ]
      in
      C (aux 1) aux
    [ k=0 → λ i → coe 0 i d in λ j → C (square j 1) (square j)
    | k=1 → refl
    ]
