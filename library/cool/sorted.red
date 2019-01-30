import prelude
import data.list
import data.nat
import data.unit
import data.bool
import data.void
import data.or
import paths.bool
import cool.insert
import cool.order
import cool.nats


def In (A : type) : (a : A) → (l : list A) → type =
  λ a → elim [
  | nil → void
  | cons x (xs → f) →
    or (path _ a x) f
  ]

def sorted (A : type) (ord : total/order A) : list A → type =
  elim [
  | nil → unit
  | cons x (xs → f) →
    elim xs [
    | nil → unit
    | cons y ys → path _ (ord.fst x y) tt × f
    ]
  ]

def sorted/swap (A : type) (ord : total/order A) (x y : A) : (ys : list A) →
  sorted A ord (cons y ys) → path _ (ord.fst x y) tt → sorted A ord (cons x ys) =
  elim [
  | nil → λ _ _ → ★
  | cons k ks → λ p1 p2 →
    let p3 = ord.snd.snd.snd x y k p2 (p1.fst) in
    (p3, p1.snd)
  ]

def sorted/skip (A : type) (ord : total/order A) (a x : A) : (xs : list A) →
  sorted A ord (cons a (cons x xs)) → sorted A ord (cons a xs) =
  elim [
  | nil → λ _ → ★
  | cons y ys → λ p →
    let p1 = ord.snd.snd.snd a x y (p.fst) (p.snd.fst) in
    let p2 = p.snd.snd in
    (p1,p2)
  ]

def min/head (A : type) (ord : total/order A) (x : A) : (xs : list A) →
  sorted A ord (cons x xs) → (y : A) → In A y xs → path _ (ord.fst x y) tt =
  elim [
  | nil → λ _ _ → elim []
  | cons k (ks → f) → λ p y p1 →
    elim p1 [
    | inl p2 → coe 1 0 (p.fst) in λ i → path _ (ord.fst x (p2 i)) tt
    | inr p2 →
      let p3 = sorted/skip A ord x k ks p in
      f p3 y p2
    ]
  ]

def In/ins (A : type) (ord : total/order A) (a y : A) : (xs : list A) → In A y (insert A ord a xs) →
  In A y (cons a xs) =
  elim [
  | nil → λ p → p
  | cons k (ks → f) → λ p →
    let convoy : (b : bool) → (path _ (ord.fst a k) b) → In A y (cons a (cons k ks)) =
    elim [
    | tt → λ p1 → coe 0 1 p in λ i → In A y (
      elim (p1 i) [
      | tt → cons a (cons k ks)
      | ff → cons k (insert A ord a ks)
      ])
    | ff → λ p1 →
      let p2 = coe 0 1 p in λ i → In A y (
      elim (p1 i) [
      | tt → cons a (cons k ks)
      | ff → cons k (insert A ord a ks)
      ]) in
      elim p2 [
      | inl p → inr (inl p)
      | inr p →
        elim (f p) [
        | inl p → inl p
        | inr p → inr (inr p)
        ]
      ]
    ]
    in convoy (ord.fst a k) refl
  ]

def sorted/tail (A : type) (ord : total/order A) (x : A) : (l : list A) → sorted A ord (cons x l)
  → sorted A ord l =
  elim [
  | nil → λ p → p
  | cons y ys → λ p → p.snd
  ]

def insert/sorted (A : type) (ord : total/order A) : (a : A) → (l : list A) →
  sorted A ord l → sorted A ord (insert A ord a l) =
  λ a → elim [
  | nil → λ _ → ★
  | cons x (xs → f) → λ p →
    let convoy : (b : bool) → (path _ (ord.fst a x) b) → sorted A ord (insert A ord a (cons x xs)) =
    elim [
    | tt → λ p1 →
      coe 1 0 (p1,p) in λ i → sorted A ord (
      elim (p1 i) [
      | tt → cons a (cons x xs)
      | ff → cons x (insert A ord a xs)
      ])
    | ff → λ p1 →
      let convoy : (l : list A) → path _ (insert A ord a xs) l →
        sorted A ord (cons x (insert A ord a xs)) =
        elim [
        | nil → λ p2 → coe 1 0 ★ in λ i → sorted A ord (cons x (p2 i))
        | cons y ys → λ p3 →
          let p4 = coe 1 0 (inl refl) in λ i → In A y (p3 i) in
          let p5 = In/ins A ord a y xs p4 in
          let p6 =
            elim p5 [
            | inl p6 →
              let p7 = total/tt/ff A ord a x p1 in
              coe 1 0 p7 in λ i → path _ (ord.fst x (p6 i)) tt
            | inr p6 → min/head A ord x xs p y p6
            ] in
          let p7 = f (sorted/tail A ord x xs p) in
          let p8 = coe 0 1 p7 in λ i → sorted A ord (p3 i) in
          coe 1 0 (p6,p8) in λ i → sorted A ord (cons x (p3 i))
        ]
      in
      let p3 = convoy (insert A ord a xs) refl in
      coe 1 0 p3 in λ i → sorted A ord (
      elim (p1 i) [
      | tt → cons a (cons x xs)
      | ff → cons x (insert A ord a xs)
      ])

    ]
    in convoy (ord.fst a x) refl
  ]

def sort/sorted (A : type) (ord : total/order A) : (l : list A) → sorted A ord (sort A ord l) =
  elim [
  | nil → ★
  | cons x (xs → f) → insert/sorted A ord x (sort A ord xs) f
  ]


