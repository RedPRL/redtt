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
    p x i

let symm/filler
  (A : type)
  (p : dim → A)
  (j, i : dim)
  : A
  =
  comp 0 j (p 0) [
  | i=0 ⇒ λ i → p i
  | i=1 ⇒ λ _ → p 0
  ]

let symm
  (A : type)
  (p : dim → A)
  : Path A (p 1) (p 0)
  =
  λ i →
    symm/filler _ p 1 i

let symm/unit
  (A : type)
  (a : A)
  : (Path (Path _ a a) (λ _ → a) (symm _ (λ _ → a)))
  =
  λ i j →
    symm/filler _ (λ _ → a) i j

let trans/filler
  (A : type)
  (p : dim → A)
  (q : [i] A [ i=0 ⇒ p 1 ])
  (j, i : dim)
  : A
  =
  comp 0 j (p i) [
  | i=0 ⇒ λ _ → p 0
  | i=1 ⇒ λ i → q i
  ]

let trans
  (A : type)
  (p : dim → A)
  (q : [i] A [ i=0 ⇒ p 1 ])
  : Path _ (p 0) (q 1)
  =
  λ i →
    trans/filler _ p q 1 i

let trans/unit/r
  (A : type)
  (p : dim → A)
  : Path (Path _ (p 0) (p 1)) (λ i → p i) (trans _ p (λ _ → p 1))
  =
  λ i j →
    trans/filler _ p (λ _ → p 1) i j

; This proof gets simpler when dead tubes are deleted!
let trans/sym/r
  (A : type)
  (p : dim → A)
  : Path (Path _ (p 0) (p 0)) (λ _ → p 0) (trans _ p (symm _ p))
  =
  λ k i →
    comp 0 1 (p i) [
    | i=0 ⇒ λ _ → p 0
    | i=1 ⇒ λ j → symm A p j
    | k=0 ⇒ λ j → symm/filler A p i j
    ;| k=1 ⇒ λ j → trans/filler A p (symm A p) j i
    ]

; Perhaps we could parallelize this proof? ;)
let symmd
  (A : dim → type)
  (p : (i : dim) → A i)
  : [i] symm^1 _ A i [
    | i=0 ⇒ p 1
    | i=1 ⇒ p 0
    ]
  =
  λ i →
    comp 0 1 (p 0) in (λ j → symm/filler^1 _ A j i) [
    | i=0 ⇒ λ j → p j
    | i=1 ⇒ λ _ → p 0
    ]
