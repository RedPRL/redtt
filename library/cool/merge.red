import prelude
import cool.order
import data.list
import data.bool
import data.nat
import cool.insert
import cool.sorted

def merge/aux (A : type) (ord : total/order A) : (n : nat) → (s t : list A) → list A =
  elim [
  | zero → λ _ _ → nil
  | suc (n → f) →
    elim [
    | nil → λ t → t
    | cons x xs →
      elim [
      | nil → cons x xs
      | cons y ys →
        elim (ord.fst x y) [
        | tt → cons x (f xs (cons y ys))
        | ff → cons y (f (cons x xs) ys)
        ]
      ]
    ]
  ]

def merge (A : type) (ord : total/order A) (s t : list A) : list A =
  merge/aux A ord (plus (length A s) (length A t)) s t

def merge/nil/right (A : type) (ord : total/order A) : (l : list A) →
  path _ (merge A ord l nil) l =
  elim [
  | nil → refl
  | cons x (xs → f) → refl
  ]

def merge/nil/left (A : type) (ord : total/order A) : (l : list A) →
  path _ (merge A ord nil l) l =
  elim [
  | nil → refl
  | cons x (xs → f) → refl
  ]

def merge/cons/tt (A : type) (ord : total/order A) (x y : A) : (xs ys : list A) →
  path _ (ord.fst x y) tt →
  path _ (merge A ord (cons x xs) (cons y ys)) (cons x (merge A ord xs (cons y ys)))
  =
  λ xs ys p i →
    elim (p i) [
    | tt → cons x (merge/aux A ord (plus (length A xs) (length A (cons y ys)))
      xs (cons y ys))
    | ff → cons y (merge/aux A ord (plus (length A xs) (length A (cons y ys))) (cons x xs) ys)
    ]

def merge/cons/ff (A : type) (ord : total/order A) (x y : A) : (xs ys : list A) →
  path _ (ord.fst x y) ff →
  path _ (merge A ord (cons x xs) (cons y ys)) (cons y (merge A ord (cons x xs) ys))
  =
  λ xs ys p i →
    elim (p i) [
    | tt → cons x (merge/aux A ord (plus (length A xs) (length A (cons y ys)))
      xs (cons y ys))
    | ff →
      let p1 = plus/suc/r (length A xs) (length A ys) in
      cons y (merge/aux A ord (p1 i) (cons x xs) ys)
    ]

def insert/tt (A : type) (ord : total/order A) (x y : A) : (l : list A) →
  path _ (ord.fst x y) tt → path _ (insert A ord x (cons y l)) (cons x (cons y l)) =
   λ l p →
    λ i → elim (p i) [
    | tt → cons x (cons y l)
    | ff → cons y (insert A ord x l)
    ]

def insert/ff (A : type) (ord : total/order A) (x y : A) : (l : list A) →
  path _ (ord.fst x y) ff → path _ (insert A ord x (cons y l)) (cons y (insert A ord x l))
  = λ l p →
    λ i → elim (p i) [
    | tt → cons x (cons y l)
    | ff → cons y (insert A ord x l)
    ]

def merge/cons/insert (A : type) (ord : total/order A) (x : A) : (xs l : list A) →
  sorted A ord (cons x xs) →
  path _ (merge A ord (cons x xs) l) (insert A ord x (merge A ord xs l)) =
  let ins = insert A ord in
  let mer = merge A ord in
  elim [
  | nil →
    elim [
    | nil → λ _ → merge/nil/right A ord (cons x nil)
    | cons t (ts → f) → λ _ →
      let convoy : (b : bool) → path _ (ord.fst x t) b →
      path _ (merge A ord (cons x nil) (cons t ts)) (insert A ord x (cons t ts)) =
      elim [
      | tt → λ p →
        let p1 = merge/cons/tt A ord x t nil ts p in
        let p2 = insert/tt A ord x t ts p in
        trans _ p1 (symm _ p2)
      | ff → λ p →
        let p1 = merge/cons/ff A ord x t nil ts p in
        let p2 = insert/ff A ord x t ts p in
        let p3 : path _ (insert A ord x (merge A ord nil ts)) (insert A ord x ts)
          = λ i → insert A ord x (merge/nil/left A ord ts i) in
        let p4 = trans _ (f ★) p3 in
        let p5 : path (list A) (cons t (merge A ord (cons x nil) ts))
          (cons t (insert A ord x ts)) = λ i → cons t (p4 i) in
        trans _ p1 (trans _ p5 (symm _ p2))
      ]

      in convoy (ord.fst x t) refl
    ]
  | cons y ys →
    elim [
    | nil → λ s →
      let p1 = merge/nil/right A ord (cons x (cons y ys)) in
      let p2 = merge/nil/right A ord (cons y ys) in
      let p3 : path _ (ins x (p2 0)) (ins x (p2 1)) = λ i → ins x (p2 i) in
      let p4 = insert/tt A ord x y ys (s.fst) in
      trans _ p1 (trans _ (symm _ p4) (symm _ p3))
    | cons t (ts → f) → λ s →
      let motive : type =
        path _ (mer (cons x (cons y ys)) (cons t ts))
               (ins x (mer (cons y ys) (cons t ts))) in
      let convoy : (b1 : bool) → path _ (ord.fst x t) b1 → (b2 : bool) →
        path _ (ord.fst y t) b2 → motive
        =
        elim [
        | tt → λ p1 →
          let p3 = merge/cons/tt A ord x t (cons y ys) ts p1 in
          elim [
          | tt → λ p2 →
            let p4 = merge/cons/tt A ord y t ys ts p2 in
            let p5 : path (list A) (cons x (p4 0)) (cons x (p4 1))
              = λ i → cons x (p4 i) in
            let p6 = insert/tt A ord x y (mer ys (cons t ts)) (s.fst) in
            let p7 : path _ (ins x (p4 0)) (ins x (p4 1)) = λ i → ins x (p4 i) in
            let p8 = trans _ p3 p5 in
            trans _ p8 (trans _ (symm _ p6) (symm _ p7))
          | ff → λ p2 →
            let p4 = merge/cons/ff A ord y t ys ts p2 in
            let p5 : path (list A) (cons x (p4 0)) (cons x (p4 1))
              = λ i → cons x (p4 i) in
            let p6 = insert/tt A ord x t (mer (cons y ys) ts) p1 in
            let p7 : path _ (ins x (p4 0)) (ins x (p4 1)) = λ i → ins x (p4 i) in
            let p8 = trans _ p3 p5 in
            trans _ p8 (trans _ (symm _ p6) (symm _ p7))
          ]
        | ff → λ p1 _ _ →
          let p2 = total/tt/ff A ord x t p1 in
          let convoy : (b : bool) → path _ (ord.fst y t) b → motive =
            elim [
            | tt → λ p →
              let p3 = total/cycle A ord t x y p2 (s.fst) p in
              elim (total/ff/eq A ord x t p1 (symm _ (p3.fst))) []
            | ff → λ p →
              let p3 = ord.snd.snd.snd t x y p2 (s.fst) in
              let p4 = merge/cons/ff A ord y t ys ts p in
              let p5 = merge/cons/ff A ord x t (cons y ys) ts p1 in
              let p6 = insert/ff A ord x t (mer (cons y ys) ts) p1 in
              let p7 : path _ (ins x (p4 0)) (ins x (p4 1)) = λ i → ins x (p4 i) in
              let p8 : path (list A) (cons t (f s 0)) (cons t (f s 1)) = λ i → cons t (f s i) in
              trans _ p5 (trans _ p8 (trans _ (symm _ p6) (symm _ p7)))
            ]
          in convoy (ord.fst y t) refl
        ]
      in convoy (ord.fst x t) refl (ord.fst y t) refl
    ]
  ]

def merge/insert/comm (A : type) (ord : total/order A) (x : A) : (xs l : list A) →
  sorted A ord xs →
  path _ (merge A ord (insert A ord x xs) l) (insert A ord x (merge A ord xs l)) =
  let ins = insert A ord in
  let mer = merge A ord in
  elim [
  | nil → λ l _ → merge/cons/insert A ord x nil l ★
  | cons y (ys → f) → λ l s →
    let convoy : (b : bool) → path _ (ord.fst x y) b →
      path _ (mer (ins x (cons y ys)) l) (ins x (mer (cons y ys) l)) =
      elim [
      | tt → λ p →
        let p1 = insert/tt A ord x y ys p in
        let p2 : path _ (mer (p1 0) l) (mer (p1 1) l) = λ i → mer (p1 i) l in
        let p3 = merge/cons/insert A ord x (cons y ys) l (p,s) in
        trans _ p2 p3
      | ff → λ p →
        let p1 = insert/ff A ord x y ys p in
        let p2 : path _ (mer (p1 0) l) (mer (p1 1) l) = λ i → mer (p1 i) l in
        let s1 = coe 0 1 (insert/sorted A ord x (cons y ys) s) in λ i → sorted A ord (p1 i) in
        let p3 = merge/cons/insert A ord y (ins x ys) l s1 in
        let s2 = sorted/tail A ord y ys s in
        let p4 = trans _ p3 (λ i → ins y (f l s2 i)) in
        let p5 = merge/cons/insert A ord y ys l s in
        let p6 = insert/comm A ord y x (mer ys l) in
        trans _ p2 (trans _ p4 (trans _ p6 (symm _ (λ i → ins x (p5 i)))))

      ]
    in convoy (ord.fst x y) refl
  ]

def insert/inorder (A : type) (ord : total/order A) (x : A) : (l : list A) →
  sorted A ord (cons x l) → path _ (insert A ord x l) (cons x l) =
  elim [
  | nil → λ s → refl
  | cons y (ys → f) → λ s →
    λ i → elim (s.fst i) [
    | tt → cons x (cons y ys)
    | ff → cons y (insert A ord x ys)
    ]
  ]

def merge/cons/swap (A : type) (ord : total/order A) (x : A) : (l r : list A) →
  sorted A ord (cons x l) → sorted A ord (cons x r) → path _ (merge A ord (cons x l) r)
  (merge A ord l (cons x r)) =
  let ins = insert A ord in
  let mer = merge A ord in
  elim [
  | nil → λ r _ s2 →
    let p1 = merge/cons/insert A ord x nil r ★ in
    let p2 = merge/nil/left A ord r in
    let p3 = insert/inorder A ord x r s2 in
    let p4 = merge/nil/left A ord (cons x r) in
    trans _ p1 (trans _ (λ i → ins x (p2 i)) (trans _ p3 (symm _ p4)))

  | cons t (ts → f) → λ r s1 s2 →
    let s3 = sorted/skip A ord x t ts s1 in
    let s4 = sorted/tail A ord x (cons t ts) s1 in
    let p1 = merge/cons/insert A ord t ts (cons x r) s4 in
    let p2 = f r s3 s2 in
    let p3 = merge/cons/insert A ord x ts r s3 in
    let p4 = merge/cons/insert A ord x (cons t ts) r s1 in
    let p5 = merge/cons/insert A ord t ts r s4 in
    let p6 : path _ (ins t (ins x (mer ts r))) (ins t (mer ts (cons x r))) =
      λ i → ins t ((trans _ (symm _ p3) p2) i) in
    let p7 = trans _ p4 (λ i → ins x (p5 i)) in
    trans _ p7 (trans _ (insert/comm A ord x t (mer ts r)) (trans _ p6 (symm _ p1)))
  ]

def merge/sorted/comm (A : type) (ord : total/order A) : (l r : list A) →
  sorted A ord l → sorted A ord r → path _ (merge A ord l r) (merge A ord r l) =
  let mer = merge A ord in
  elim [
  | nil → λ r _ _ → trans _ (merge/nil/left A ord r) (symm _ (merge/nil/right A ord r))
  | cons x (xs → f) →
    elim [
    | nil → λ _ _ → trans _ (merge/nil/right A ord (cons x xs)) (symm _ (merge/nil/left A ord (cons x xs)))
    | cons y (ys → f1) → λ s1 s2 →
      let convoy : (b1 : bool) → path _ (ord.fst x y) b1 → (b2 : bool) → path _ (ord.fst y x) b2 →
        path _ (mer (cons x xs) (cons y ys)) (mer (cons y ys) (cons x xs)) =
        elim [
        | tt → λ p1 →
          let p = merge/cons/tt A ord x y xs ys p1 in
          elim [
          | tt → λ p2 →
            let p3 = ord.snd.fst x y (trans _ p1 (symm _ p2)) in
            let p4 = merge/cons/tt A ord y x ys xs p2 in
            let p5 = f (cons y ys) (sorted/tail A ord x xs s1) s2 in
            let p6 : path (list A) (cons x (mer (cons y ys) xs)) (cons y (mer (cons x ys) xs)) =
              λ i → cons (p3 i) (mer (cons (symm _ p3 i) ys) xs) in
            let p7 : path (list A)(cons x (p5 0)) (cons x (p5 1)) = λ i → cons x (p5 i) in
            let s3 : sorted A ord (cons x ys) = coe 1 0 s2 in λ i → sorted A ord (cons (p3 i) ys) in
            let p8 = merge/cons/swap A ord x ys xs s3 s1 in
            let p9 : path (list A) (cons y (p8 0)) (cons y (p8 1)) = λ i → cons y (p8 i) in
            trans _ p (trans _ p7 (trans _ p6 (trans _ p9 (symm _ p4))))
          | ff → λ p2 →
            let p3 = merge/cons/ff A ord y x ys xs p2 in
            let p4 = f (cons y ys) (sorted/tail A ord x xs s1) s2 in
            let p5 : path (list A) (cons x (p4 0)) (cons x (p4 1)) = λ i → cons x (p4 i) in
            trans _ p (trans _ p5 (symm _ p3))
          ]
        | ff → λ p1 _ _ →
          let p2 = total/tt/ff A ord x y p1 in
          let p3 = merge/cons/ff A ord x y xs ys p1 in
          let p4 = merge/cons/tt A ord y x ys xs p2 in
          let p5 = f1 s1 (sorted/tail A ord y ys s2) in
          let p6 : path (list A) (cons y (p5 0)) (cons y (p5 1)) =
            λ i → cons y (p5 i) in
          trans _ p3 (trans _ p6 (symm _ p4))
        ]
      in convoy (ord.fst x y) refl (ord.fst y x) refl
    ]
  ]

