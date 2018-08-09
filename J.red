import path

let J
  (A : type) (a : A)
  (C : (x : A) (p : Path _ a x) → type) (d : C a (λ _ → a))
  (x : A) (p : Path _ a x)
  : C x p
  =
  let ty : dim → type = λ i →
    let h : dim → A = λ j →
      comp 0 j a [
      | i=0 ⇒ λ _ → a
      | i=1 ⇒ λ k → p k
      ]
    in
    C (h 1) (λ k → h k)
  in
  coe 0 1 d in ty

let J/eq
  (A : type) (a : A)
  (C : (x : A) (p : Path A a x) → type) (d : C a (λ _ → a))
  : Path (C a _) (J _ _ C d _ (λ _ → a)) d
  =
  let square : dim → dim → A =
    λ i j →
      comp 0 j a [
      | i=0 ⇒ λ _ → a
      | i=1 ⇒ λ _ → a
      ]
  in
  λ k →
    comp 0 1 d in λ i →
      let aux : dim → A =
        λ j →
          comp 0 j a [
          | k=0 ⇒ λ l → square i l
          | k=1 ⇒ λ _ → a
          | i=0 ⇒ λ _ → a
          | i=1 ⇒ λ _ → a
          ]
      in
      C (aux 1) (λ l → aux l)
    with
    | k=0 ⇒ λ i →
      coe 0 i d in λ j →
        C (square j 1) (λ k → square j k)
    | k=1 ⇒ λ _ → d
    end
