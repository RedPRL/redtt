import prelude
import cool.order
import data.list
import data.bool

def insert (A : type) (ord : total/order A)  : A → list A → list A =
  λ a → elim [
  | nil → cons a nil
  | cons x (xs → f) →
    elim (ord.fst a x) [
    | tt → cons a (cons x xs)
    | ff → cons x f
    ]
  ]

def sort (A : type) (ord : total/order A) : list A → list A =
  elim [
  | nil → nil
  | cons x (xs → f) →
    insert A ord x f
  ]

def perm (A : type) (ord : total/order A) (l k : list A) : type =
  path _ (sort A ord l) (sort A ord k)

def insert/comm (A : type) (ord : total/order A) (a b : A) : (l : list A) →
  path _ (insert A ord a (insert A ord b l)) (insert A ord b (insert A ord a l)) =
  let r = ord.fst in
  elim [
  | nil →
    let convoy : (b1 b2 : bool) → path _ (r a b) b1 → path _ (r b a) b2 →
      path _ (insert A ord a (cons b nil)) (insert A ord b (cons a nil)) =
      elim [
      | tt →
        elim [
        | tt → λ p1 p2 →
        let p3 = ord.snd.fst a b (trans _ p1 (symm _ p2)) in
        let p4 = symm _ p3 in
        λ i → elim (r (p3 i) (p4 i)) [
        | tt → cons (p3 i) (cons (p4 i) nil)
        | ff → cons (p4 i) (cons (p3 i) nil)
        ]

        | ff → λ p1 p2 →
        let p3 : path _ (insert A ord a (cons b nil)) (cons a (cons b nil)) = λ i →
          elim (p1 i) [
          | tt → cons a (cons b nil)
          | ff → cons b (cons a nil)
          ]
        in
        let p4 : path _ (insert A ord b (cons a nil)) (cons a (cons b nil)) = λ i →
          elim (p2 i) [
          | tt → cons b (cons a nil)
          | ff → cons a (cons b nil)
          ]
        in
          trans _ p3 (symm _ p4)
        ]
      | ff →
        elim [
        | tt → λ p1 p2 →
        let p3 : path _ (insert A ord a (cons b nil)) (cons b (cons a nil)) = λ i →
          elim (p1 i) [
          | tt → cons a (cons b nil)
          | ff → cons b (cons a nil)
          ]
        in
        let p4 : path _ (insert A ord b (cons a nil)) (cons b (cons a nil)) = λ i →
          elim (p2 i) [
          | tt → cons b (cons a nil)
          | ff → cons a (cons b nil)
          ]
        in
          trans _ p3 (symm _ p4)

        | ff → λ p1 p2 →
        let p3 = ord.snd.fst a b (trans _ p1 (symm _ p2)) in
        let p4 = symm _ p3 in
        λ i → elim (r (p3 i) (p4 i)) [
        | tt → cons (p3 i) (cons (p4 i) nil)
        | ff → cons (p4 i) (cons (p3 i) nil)
        ]
        ]
      ]
    in convoy (r a b) (r b a) refl refl
  | cons x (xs → f) →
    let l : list A = cons x xs in
    let convoy : (b1 b2 b3 b4 : bool) →
      path _ (r a b) b1 → path _ (r b a) b2 →
      path _ (r a x) b3 → path _ (r b x) b4 →
      path _ (insert A ord a (insert A ord b l)) (insert A ord b (insert A ord a l)) =
      elim [
      | tt →
        elim [
        | tt → λ b3 b4 p1 p2 p3 p4 →
          let p5 = ord.snd.fst a b (trans _ p1 (symm _ p2)) in
          let p6 = symm _ p5 in
          λ i → insert A ord (p5 i) (insert A ord (p6 i) l)
        | ff →
          elim [
          | tt →
            elim [
            | tt → λ p1 p2 p3 p4 →
              let p5 : path _ (insert A ord b l) (cons b l) =
              λ i →
                elim (p4 i) [
                | tt → cons b l
                | ff → cons x (insert A ord b xs)
                ]
              in
              let p6 : path _ (insert A ord a l) (cons a l) =
              λ i →
              elim (p3 i) [
              | tt → cons a l
              | ff → cons x (insert A ord a xs)
              ]
              in
              let p7 : path _ (insert A ord a (cons b l)) (cons a (cons b l)) =
              λ i → elim (p1 i) [
              | tt → cons a (cons b l)
              | ff → cons b (insert A ord a l)
              ] in
              let p8 : path _ (insert A ord b (cons a l)) (cons a (cons b l)) =
              λ i → elim (p2 i) [
              | tt → cons b (cons a l)
              | ff → cons a (p5 i)
              ] in
              let p5' : path _ (insert A ord a (p5 0))
                      (insert A ord a (p5 1)) = λ i → insert A ord a (p5 i) in
              let p6' : path _ (insert A ord b (p6 0))
                      (insert A ord b (p6 1)) = λ i → insert A ord b (p6 i) in
              let p9 = trans _ p5' p7 in
              let p10 = trans _ p6' p8 in
              trans _ p9 (symm _ p10)
            | ff → λ p1 p2 p3 p4 →
              let p5 : path _ (insert A ord b l) (cons x (insert A ord b xs)) =
              λ i →
                elim (p4 i) [
                | tt → cons b l
                | ff → cons x (insert A ord b xs)
                ]
              in
              let p6 : path _ (insert A ord a l) (cons a l) =
              λ i →
              elim (p3 i) [
              | tt → cons a l
              | ff → cons x (insert A ord a xs)
              ]
              in
              let p7 : path _ (insert A ord a (p5 1)) (cons a (p5 1)) =
              λ i → elim (p3 i) [
              | tt → cons a (p5 1)
              | ff → cons x (insert A ord a (insert A ord b xs))
              ] in
              let p8 : path _ (insert A ord b (cons a l))
                (cons a (p5 1)) =
              λ i → elim (p2 i) [
              | tt → cons b (cons a l)
              | ff → cons a (p5 i)
              ] in
              let p5' : path _ (insert A ord a (p5 0))
                      (insert A ord a (p5 1)) = λ i → insert A ord a (p5 i) in
              let p6' : path _ (insert A ord b (p6 0))
                      (insert A ord b (p6 1)) = λ i → insert A ord b (p6 i) in
              let p9 = trans _ p5' p7 in
              let p10 = trans _ p6' p8 in
              trans _ p9 (symm _ p10)
            ]
          | ff →
            elim [
            | tt → λ p1 p2 p3 p4 →
              let p5 = total/tt/ff A ord a x p3 in
              let g = total/cycle A ord x a b p5 p1 p4 in
              let xa = g.fst in
              let xb = g.snd in
              let ab = trans _ (symm _ xa) xb in
              let ba = symm _ ab in
              λ i → insert A ord (ab i) (insert A ord (ba i) l)

            | ff → λ p1 p2 p3 p4 →
              let p5 : path _ (insert A ord b l) (cons x (insert A ord b xs)) =
              λ i →
                elim (p4 i) [
                | tt → cons b l
                | ff → cons x (insert A ord b xs)
                ]
              in
              let p6 : path _ (insert A ord a l) (cons x (insert A ord a xs)) =
              λ i →
              elim (p3 i) [
              | tt → cons a l
              | ff → cons x (insert A ord a xs)
              ]
              in
              let p7 : path _ (insert A ord a (p5 1))
                              (cons x (insert A ord a (insert A ord b xs))) =
              λ i → elim (p3 i) [
              | tt → cons a (p5 1)
              | ff → cons x (insert A ord a (insert A ord b xs))
              ] in
              let p8 : path _ (insert A ord b (p6 1))
                (cons x (insert A ord b (insert A ord a xs))) =
              λ i → elim (p4 i) [
              | tt → cons b (p6 1)
              | ff → cons x (insert A ord b (insert A ord a xs))
              ] in
              let p5' : path _ (insert A ord a (p5 0))
                      (insert A ord a (p5 1)) = λ i → insert A ord a (p5 i) in
              let p6' : path _ (insert A ord b (p6 0))
                      (insert A ord b (p6 1)) = λ i → insert A ord b (p6 i) in
              let p9 = trans _ p5' p7 in
              let p10 : path (list A) (cons x (insert A ord a (insert A ord b xs)))
              (cons x (insert A ord b (insert A ord a xs))) = λ i → cons x (f i) in
              let p11 = trans _ p9 p10 in
              let p12 = trans _ p6' p8 in
              trans _ p11 (symm _ p12)
            ]
          ]
        ]
      | ff →
        elim [
        | tt →
          elim [
          | tt →
            elim [
            | tt → λ p1 p2 p3 p4 →
              let p5 : path _ (insert A ord b l) (cons b l) =
              λ i →
                elim (p4 i) [
                | tt → cons b l
                | ff → cons x (insert A ord b xs)
                ]
              in
              let p6 : path _ (insert A ord a l) (cons a l) =
              λ i →
              elim (p3 i) [
              | tt → cons a l
              | ff → cons x (insert A ord a xs)
              ]
              in
              let p7 : path _ (insert A ord a (cons b l)) (cons b (cons a l)) =
              λ i → elim (p1 i) [
              | tt → cons a (cons b l)
              | ff → cons b (p6 i)
              ] in
              let p8 : path _ (insert A ord b (cons a l)) (cons b (cons a l)) =
              λ i → elim (p2 i) [
              | tt → cons b (cons a l)
              | ff → cons a (p5 i)
              ] in
              let p5' : path _ (insert A ord a (p5 0))
                      (insert A ord a (p5 1)) = λ i → insert A ord a (p5 i) in
              let p6' : path _ (insert A ord b (p6 0))
                      (insert A ord b (p6 1)) = λ i → insert A ord b (p6 i) in
              let p9 = trans _ p5' p7 in
              let p10 = trans _ p6' p8 in
              trans _ p9 (symm _ p10)
            | ff →  λ p1 p2 p3 p4 →
              let p5 = total/tt/ff A ord b x p4 in
              let g = total/cycle A ord b a x p2 p3 p5 in
              let ba = g.fst in
              let ab = symm _ ba in
              λ i → insert A ord (ab i) (insert A ord (ba i) l)
            ]
          | ff →
            elim [
            | tt → λ p1 p2 p3 p4 →
              let p5 : path _ (insert A ord b l) (cons b l) =
              λ i →
                elim (p4 i) [
                | tt → cons b l
                | ff → cons x (insert A ord b xs)
                ]
              in
              let p6 : path _ (insert A ord a l) (cons x (insert A ord a xs)) =
              λ i →
              elim (p3 i) [
              | tt → cons a l
              | ff → cons x (insert A ord a xs)
              ]
              in
              let p7 : path _ (insert A ord a (cons b l))
                (cons b (cons x (insert A ord a xs))) =
              λ i → elim (p1 i) [
              | tt → cons a (cons b l)
              | ff → cons b (p6 i)
              ] in
              let p8 : path _ (insert A ord b (p6 1)) (cons b (p6 1)) =
              λ i → elim (p4 i) [
              | tt → cons b (p6 1)
              | ff → cons x (insert A ord b (insert A ord a xs))
              ] in
              let p5' : path _ (insert A ord a (p5 0))
                      (insert A ord a (p5 1)) = λ i → insert A ord a (p5 i) in
              let p6' : path _ (insert A ord b (p6 0))
                      (insert A ord b (p6 1)) = λ i → insert A ord b (p6 i) in
              let p9 = trans _ p5' p7 in
              let p10 = trans _ p6' p8 in
              trans _ p9 (symm _ p10)

            | ff → λ p1 p2 p3 p4 →
              let p5 : path _ (insert A ord b l) (cons x (insert A ord b xs)) =
              λ i →
                elim (p4 i) [
                | tt → cons b l
                | ff → cons x (insert A ord b xs)
                ]
              in
              let p6 : path _ (insert A ord a l) (cons x (insert A ord a xs)) =
              λ i →
              elim (p3 i) [
              | tt → cons a l
              | ff → cons x (insert A ord a xs)
              ]
              in
              let p7 : path _ (insert A ord a (p5 1))
                              (cons x (insert A ord a (insert A ord b xs))) =
              λ i → elim (p3 i) [
              | tt → cons a (p5 1)
              | ff → cons x (insert A ord a (insert A ord b xs))
              ] in
              let p8 : path _ (insert A ord b (p6 1))
                (cons x (insert A ord b (insert A ord a xs))) =
              λ i → elim (p4 i) [
              | tt → cons b (p6 1)
              | ff → cons x (insert A ord b (insert A ord a xs))
              ] in
              let p5' : path _ (insert A ord a (p5 0))
                      (insert A ord a (p5 1)) = λ i → insert A ord a (p5 i) in
              let p6' : path _ (insert A ord b (p6 0))
                      (insert A ord b (p6 1)) = λ i → insert A ord b (p6 i) in
              let p9 = trans _ p5' p7 in
              let p10 : path (list A) (cons x (insert A ord a (insert A ord b xs)))
              (cons x (insert A ord b (insert A ord a xs))) = λ i → cons x (f i) in
              let p11 = trans _ p9 p10 in
              let p12 = trans _ p6' p8 in
              trans _ p11 (symm _ p12)
          ]
          ]
        | ff → λ  b3 b4 p1 p2 p3 p4 →
          let p5 = ord.snd.fst a b (trans _ p1 (symm _ p2)) in
          let p6 = symm _ p5 in
          λ i → insert A ord (p5 i) (insert A ord (p6 i) l)
        ]
      ]

    in
    convoy (r a b) (r b a) (r a x) (r b x) refl refl refl refl
  ]

def insert/swap (A : type) (ord : total/order A) (x y : A) (l : list A) :
  perm A ord (cons x (cons y l)) (cons y (cons x l)) =
  insert/comm A ord x y (sort A ord l)

def insert/sort/comm (A : type) (ord : total/order A) (a : A) : (l : list A) →
  path _ (insert A ord a (sort A ord l)) (sort A ord (insert A ord a l)) =
  elim [
  | nil → refl
  | cons x (xs → f) →
    let l : list A = cons x xs in
    let r = ord.fst in
    let convoy : (b : bool) → path _ (r a x) b →
    path _ (insert A ord a (sort A ord l)) (sort A ord (insert A ord a l)) =
    elim [
    | tt → λ p →
      let p1 : path _ (insert A ord a (cons x xs)) (cons a (cons x xs)) =
        λ i → elim (p i) [
        | tt → cons a (cons x xs)
        | ff → cons x (insert A ord a xs)
        ]
      in
      λ i → sort A ord ((symm _ p1) i)
    | ff → λ p →
      let p1 : path _ (insert A ord a (cons x xs)) (cons x (insert A ord a xs)) =
        λ i → elim (p i) [
        | tt → cons a (cons x xs)
        | ff → cons x (insert A ord a xs)
        ]
      in
      let p2 : path _ (sort A ord (p1 0)) (sort A ord (p1 1)) = λ i → sort A ord (p1 i) in
      let p3 = insert/comm A ord a x (sort A ord xs)  in
      let p4 : path _ (insert A ord x (f 0)) (insert A ord x (f 1)) =
        λ i → insert A ord x (f i) in
      let p5 = trans _ p4 (symm _ p2) in
      trans _ p3 p5
    ]
    in convoy (r a x) refl
  ]

def sort/swap (A : type) (ord : total/order A) (x y : A) : (xs ys : list A) →
  perm A ord (append A (cons x xs) (cons y ys)) (append A (cons y xs) (cons x ys)) =
  elim [
  | nil → λ ys → insert/swap A ord x y ys
  | cons x' (xs' → f) → λ ys →
    let p1 = insert/comm A ord x x' (sort A ord (append A xs' (cons y ys))) in
    let p2 = insert/comm A ord y x' (sort A ord (append A xs' (cons x ys))) in
    let p3 : path _ (insert A ord x' (f ys 0)) (insert A ord x' (f ys 1)) =
      λ i → insert A ord x' (f ys i) in
    let p4 = trans _ p1 p3 in
    trans _ p4 (symm _ p2)
  ]

def sort/cons (A : type) (ord : total/order A) : (a : A) (s t : list A) → perm A ord s t →
  perm A ord (cons a s) (cons a t) =
  λ a s t p → λ i → insert A ord a (p i)

def merge (A : type) (ord : total/order A) : (s t : list A) →
  ((l : list A) × perm A ord l (append A s t)) =
  elim [
  | nil → λ t → (t,refl)
  | cons x (xs → f) →
    let r = ord.fst in
    elim [
    | nil →
    let p = append/idn/r A (cons x xs) in
    let p1 : path _ (sort A ord (p 0)) (sort A ord (p 1)) = λ i → sort A ord (p i) in
    (cons x xs, symm _ p1)
    | cons y ys →
      elim (r x y) [
      | tt →
        let rec = f (cons y ys) in
        let l = rec.fst in
        let p = rec.snd in
        (cons x l, sort/cons A ord x l (append A xs (cons y ys)) p)
      | ff →
        let rec = f (cons x ys) in
        let l = rec.fst in
        let p = rec.snd in
        let p1 : path _ (insert A ord y (p 0)) (insert A ord y (p 1)) =
          λ i → insert A ord y (p i) in
        let p2 = sort/swap A ord x y xs ys in
        (cons y l, trans _ p1 (symm _ p2))

      ]
    ]
  ]

