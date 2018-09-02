import path

let J
  (A : type) (a : A)
  (C : (x : A) (p : Path _ a x) → type) (d : C a (λ _ → a))
  (x : A) (p : Path _ a x)
  : C x p
  =
  let ty : dim → type =
    λ i →
      let h : dim → A =
        λ j →
          comp 0 j a [
          | i=0 → refl
          | i=1 → p
          ]
      in
      C (h 1) h
  in
  coe 0 1 d in ty

let J/eq
  (A : type) (a : A)
  (C : (x : A) (p : Path A a x) → type) (d : C a refl)
  : Path (C a refl) (J _ _ C d _ (λ _ → a)) d
  =
  let square : dim → dim → A =
    λ i j →
      comp 0 j a [
      | i=0 → refl
      | i=1 → refl
      ]
  in
  λ k →
    comp 0 1 d in λ i →
      let aux : dim → A =
        λ j →
          comp 0 j a [
          | k=0 → square i
          | k=1 → refl
          | i=0 → refl
          | i=1 → refl
          ]
      in
      C (aux 1) aux
    with
    | k=0 →
      λ i →
        coe 0 i d in λ j →
          C (square j 1) (square j)
    | k=1 → refl
    end
