import path

let J
  (A : type) (a : A)
  (C : (x : A) (p : Path _ a x) → type) (d : C a (λ _ → a))
  (x : A) (p : Path _ a x)
  : C x p
  =
  let ty : Line type = λ i →
    let h : Line A = λ j →
      comp 0 j a with
      | i=0 ⇒ λ _ → a
      | i=1 ⇒ p
      end
    in
    C (h 1) h
  in
  coe 0 1 d in ty

let J/eq
  (A : type) (a : A)
  (C : (x : A) (p : Path A a x) → type) (d : C a (λ _ → a))
  : Path (C a _) (J _ _ C d _ (λ _ → a)) d
  =
  let square : Line (Line A) =
    λ i j →
      comp 0 j a with
      | i=0 ⇒ λ _ → a
      | i=1 ⇒ λ _ → a
      end
  in
  λ k →
    comp 0 1 d in λ i →
      let aux : Line A =
        λ j →
          comp 0 j a with
          | k=0 ⇒ square i
          | k=1 ⇒ λ _ → a
          | i=0 ⇒ λ _ → a
          | i=1 ⇒ λ _ → a
          end
      in
      C (aux 1) aux
    with
    | k=0 ⇒ λ i →
      coe 0 i d in λ j →
        C (square j 1) (λ k → square j k)
    | k=1 ⇒ λ _ → d
    end
