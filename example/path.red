let PathD (A : dim → type) (M : A 0) (N : A 1) : type =
  [i] A i [
  | i=0 ⇒ M
  | i=1 ⇒ N
  ]

let Path (A : type) (M,N : A) : type =
  [i] A [
  | i=0 ⇒ M
  | i=1 ⇒ N
  ]

let Square
  (A : type)
  (M,N : dim → A)
  (O : Path A (M 0) (N 0))
  (P : Path A (M 1) (N 1))
  : type
  =
  [i j] A [
  | j=0 ⇒ M i
  | j=1 ⇒ N i
  | i=0 ⇒ O j
  | i=1 ⇒ P j
  ]

let funext
  (A : type)
  (B : A → type)
  (f,g : (x : A) → B x)
  (p : (x : A) → Path (B x) (f x) (g x))
  : Path ((x : A) → B x) f g
  =
  λ i x →
    p _ i

let symm/filler
  (A : type)
  (p : dim → A)
  (j, i : dim)
  : A
  =
  comp 0 j (p 0) [
  | i=0 ⇒ p
  | i=1 ⇒ refl
  ]

let symm
  (A : type)
  (p : dim → A)
  : Path A (p 1) (p 0)
  =
  symm/filler _ p 1

let symm/unit
  (A : type)
  (a : A)
  : Path (Path _ a a) refl (symm _ (λ _ → a))
  =
  symm/filler _ (λ _ → a)

let trans/filler
  (A : type)
  (p : dim → A)
  (q : [i] A [ i=0 ⇒ p 1 ])
  (j, i : dim)
  : A
  =
  comp 0 j (p i) [
  | i=0 ⇒ refl
  | i=1 ⇒ q
  ]

let trans
  (A : type)
  (p : dim → A)
  (q : [i] A [ i=0 ⇒ p 1 ])
  : Path _ (p 0) (q 1)
  =
  trans/filler _ p q 1

let trans/unit/r
  (A : type)
  (p : dim → A)
  : Path (Path _ (p 0) (p 1)) p (trans _ p (λ _ → p 1))
  =
  trans/filler _ p (λ _ → p 1)

let trans/unit/l
  (A : type)
  (p : dim → A)
  : Path (Path _ (p 0) (p 1)) p (trans _ (λ _ → p 0) p)
  =
  λ k i →
  comp 0 1 (p 0) [
  | k=0 ⇒ λ j →
    comp 0 1 (p 0) [
    | j=1 ⇒ λ l → comp 0 i (p 0) [ l=0 ⇒ refl | l=1 ⇒ p ]
    | i=1 ⇒ λ l → comp 0 j (p 0) [ l=0 ⇒ refl | l=1 ⇒ p ]
    | j=0 ⇒ refl
    | i=0 ⇒ refl
    ]
  | i=0 ⇒ refl
  | i=1 ⇒ p
  ]

; This proof gets simpler when dead tubes are deleted!
let trans/sym/r
  (A : type)
  (p : dim → A)
  : Path (Path _ (p 0) (p 0)) refl (trans _ p (symm _ p))
  =
  λ k i →
    comp 0 1 (p i) [
    | i=0 ⇒ refl
    | i=1 ⇒ symm A p
    | k=0 ⇒ symm/filler A p i
    ;| k=1 ⇒ λ j → trans/filler A p (symm A p) j i
    ]

let trans/sym/l
  (A : type)
  (p : dim → A)
  : Path (Path _ (p 1) (p 1)) refl (trans _ (symm _ p) p)
  =
  λ k i →
    comp 0 1 (symm/filler A p k i) [
    | i=0 ⇒ λ j →
      comp 0 1 (p 1) [
      | j=0 ⇒ λ l → comp 1 k (p 1) [ l=0 ⇒ refl | l=1 ⇒ p ]
      | k=0 ⇒ λ l → comp 1 j (p 1) [ l=0 ⇒ refl | l=1 ⇒ p ]
      | j=1 ⇒ refl
      | k=1 ⇒ refl
      ]
    | i=1 ⇒ p
    | k=0 ⇒ p
    ;| k=1 ⇒ λ j → trans/filler A (symm A p) p j i
    ]

; Perhaps we could parallelize this proof? ;)
let symmd
  (A : dim → type)
  (p : (i : dim) → A i)
  : PathD (symm^1 _ A) (p 1) (p 0)
  =
  λ i →
    comp 0 1 (p 0) in (λ j → symm/filler^1 _ A j i) [
    | i=0 ⇒ p
    | i=1 ⇒ refl
    ]
