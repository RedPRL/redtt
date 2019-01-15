import prelude
import data.list
import data.nat
import data.unit
import cool.nat-lemmas
import data.bool
import data.void
import data.or
import paths.bool
import cool.insert
import cool.order
import cool.nats
import cool.sorted
import cool.merge

def le/bool/tt/ff : (x y : nat) → path _ (le/bool x y) ff → path _ (le/bool y x) tt = 
	elim [
	| zero → λ y p → elim (tt/ne/ff p) []
	| suc (x → f) → 
		elim [
		| zero → λ _ → refl
		| suc y → λ p → 
			let p1 = f y p in 
			let l1 = le/bool/r y x p1 in 
			let l2 = le/suc y x l1 in 
			le/bool/l (suc y) (suc x) l2 
		]
	]

def le/bool/antisymm : (x y : nat) → path _ (le/bool x y) (le/bool y x)
	→ path _ x y =
	elim [
	| zero → 
		elim [
		| zero → λ _   → refl
		| suc y → λ p → elim (tt/ne/ff p) []
		]
	| suc (x → f) → 
		elim [
		| zero → λ p → elim (tt/ne/ff (symm _ p)) []
		| suc y → λ p → 
			let convoy : (b : bool) → path _ (le/bool (suc x) (suc y)) b → 
				path nat (suc x) (suc y) = 
				elim [
				| tt → λ p1 →
					let p2 = le/bool/pred (suc x) (suc y) p1 in 
					let p3 = trans _ (symm _ p) p1 in 
					let p4 = le/bool/pred (suc y) (suc x) p3 in 
					λ i → suc (f y (trans _ p2 (symm _ p4)) i)
				| ff → λ p1 → 
					let p2 = le/bool/tt/ff (suc x) (suc y) p1 in 
					let p3 = trans _ p p2 in 
					let p4 = le/bool/pred (suc x) (suc y) p3 in 
					let p5 = le/bool/pred (suc y) (suc x) p2 in 
					λ i → suc (f y (trans _ p4 (symm _ p5)) i)
				]
			in convoy (le/bool (suc x) (suc y)) refl
			
		]
	]

def le/bool/refl : (x : nat) → path _ (le/bool x x) tt = 
	elim [
	| zero → refl
	| suc (x → f) → f
	]

def le/bool/trans : (m n l : nat) → path _ (le/bool m n) tt → 
	path _ (le/bool n l) tt → path _ (le/bool m l) tt =
  elim [
  | zero → λ _ _ _ _ → refl
  | suc (m' → f) →
    elim [
    | zero → λ _ p _ → elim (tt/ne/ff (symm _ p)) []
    | suc n' →
      elim [
      | zero → λ _ p → p
      | suc l' → f n' l'
      ]
    ]
  ]
def ord/nat : total/order nat = 
	(le/bool, le/bool/antisymm, le/bool/refl, le/bool/trans)

def ex : list nat = sort nat ord/nat (cons n3 (cons n2 (cons zero nil))) 

def insert/length (A : type) (ord : total/order A) : (a : A) → (l : list A) →
	path _ (length A (insert A ord a l)) (suc (length A l)) = 
	λ a → elim [
	| nil → refl
	| cons x (xs → f) → 
		let convoy : (b : bool) → path _ (ord.fst a x) b →  
		path _ (length A (insert A ord a (cons x xs))) (suc (suc (length A xs)))= λ b → 
		elim b [
		| tt → λ p → 
			λ i → 
			length A (elim (p i) [
			| tt → cons a (cons x xs)
			| ff → cons x (insert A ord a xs)
			])

		| ff → λ p → 
			let p1 : path _ (length A (insert A ord a (cons x xs))) 
					(suc (length A (insert A ord a xs))) = 
				λ i → 
				length A (elim (p i) [
				| tt → cons a (cons x xs)
				| ff → cons x (insert A ord a xs)
				]) in
			let p2 : path nat (suc (length A (insert A ord a xs))) 
				(suc (suc (length A xs))) = λ i → suc (f i) in 
			trans _ p1 p2
		] in convoy (ord.fst a x) refl
	]

def sort/length (A : type) (ord : total/order A) : (l : list A) → 
	path _ (length A l) (length A (sort A ord l)) = 
	elim [
	| nil → refl
	| cons x (xs → f) → 
		let p : path _ (length A (insert A ord x (sort A ord xs))) (suc (length A (sort A ord xs))) 
			= insert/length A ord x (sort A ord xs) in 
		let p1 : path nat (suc (length A xs)) (suc (length A (sort A ord xs))) 
			= λ i → suc (f i) in 
		trans _ p1 (symm _ p)
	]

def sort/nil (A : type) (ord : total/order A) : (l : list A) → path (list A) nil (sort A ord l) → 
	path (list A) nil l =
	elim [
	| nil → λ _ → refl
	| cons x xs → λ p → 
		let p1 : path nat zero (length A (sort A ord (cons x xs))) = λ i → length A (p i) in 
		let p2 = sort/length A ord (cons x xs) in
		let p3 = trans _ p1 (symm _ p2) in
		elim (zero/ne/suc (length A xs) p3) []
	]

/-
def perm/cons (A : type) (ord : total/order A) : (x : A) (s xs : list A) → 
	perm A ord (cons x xs) s → (x' : A) × (xs' : list A) × path (list A) (cons x' xs') s = 
	λ x → elim [
	| nil → λ xs p → 
		let p1 = sort/nil A ord (cons x xs) (symm _ p) in 
		let v = zero/ne/suc (length A xs) (λ i → length A (p1 i)) in 
		elim v []
	| cons y ys → λ _ _ → (y,ys,refl)
	]
	-/

	/- 
	elim [
		| nil → λ s1 s2 → 
			let p1 = merge/nil/right A ord (cons x (cons t ts)) in 
			let convoy : (b : bool) → path _ (ord.fst t x) b → 
				path _ (mer (cons x (cons t ts)) nil) (mer (cons t ts) (cons x nil)) = 
			elim [
			| tt → λ p → 
				let p2 = ord.snd.fst x t (trans _ (s1.fst) (symm _ p)) in 
				let p3 = merge/cons/tt A ord t x ts nil p in 
				let s3 = sorted/skip A ord x t ts s1 in 
				let p4 = f nil s3 s2 in 
				let p5 = symm _ (merge/nil/right A ord (cons x ts)) in 
				let p6 : path (list A) (cons x (cons t ts)) (cons t (cons x ts)) = 
					λ i → cons (p2 i) (cons (symm _ p2 i) ts) in
				let p7 : path (list A) (cons t (p5 0)) (cons t (p5 1)) = λ i → cons t (p5 i) in
				let p8 : path (list A) (cons t (p4 0)) (cons t (p4 1)) = λ i → cons t (p4 i) in
				trans _ p1 (trans _ p6 (trans _ p7 (trans _ p8 (symm _ p3))))
			| ff → λ p → 
				let p2 = merge/cons/ff A ord t x ts nil p in 
				let p3 = merge/nil/right A ord (cons t ts) in 
				let p4 : path (list A) (cons x (p3 1)) (cons x (p3 0)) = λ i → cons x (symm _ p3 i) in
				trans _ p1 (trans _  p4 (symm _ p2))
			]
			in convoy (ord.fst t x) refl

		| cons k (ks → f1) → λ s1 s2 → 
			let p1 = merge/cons/tt A ord x k (cons t ts) ks (s2.fst) in 
			let convoy : (b : bool) → path _ (ord.fst t x) b → 
				path _ (mer (cons x (cons t ts)) (cons k ks)) (mer (cons t ts) (cons x (cons k ks))) = 
				elim [
				| tt → λ p → 
				let p2 = ord.snd.fst x t (trans _ (s1.fst) (symm _ p)) in
				let p3 = merge/cons/tt A ord t x ts (cons k ks) p in
				let p4 = f (cons k ks) 
				?
				]
			in convoy (ord.fst t x) refl
			
		]
		-/

def split/aux (A : type) : nat → list A → (list A × list A) = 
	elim [
	| zero → λ _ → (nil,nil)
	| suc (n → f) → 
		elim [
		| nil → (nil, nil)
		| cons x xs → 
			elim xs [
			| nil → (cons x xs, nil)
			| cons y ys → 
			let l = (f ys).fst in
			let r = (f ys).snd in 
			(cons x l, cons y r)
			]
		]
	]

def split (A : type) : list A → (list A × list A) = λ l → split/aux A (length A l) l 

def pow2 : nat → nat = 
	elim [
	| zero → suc zero 
	| suc (n → f) → double/nat f 
	]

def split/aux/suc (A : type) : (n : nat) → (l : list A) → le (length A l) n → 
	path _ (split/aux A n l) (split/aux A (suc n) l) = 
	λ m → 
	elim m [
	| zero → 
		elim [
		| nil → refl
		| cons x xs → elim []
		]
	| suc n → 
		elim n [
		| zero → 
			elim [
			| nil → refl
			| cons x xs → 
				elim xs [
				| nil → refl
				| cons y ys → elim []
				]
			]
		| suc (n' → f) → 
			elim [
			| nil → refl
			| cons x xs → 
				elim xs [
				| nil → refl
				| cons y ys → λ p → 
					let p1 : le (length A ys) (suc n') = le/suc/right (length A ys) n' p in
					let g = f ys p1 in 
					λ i → (cons x ((g i).fst), cons y ((g i).snd))
					]
				]
		]
	]

def split/cons/cons (A : type) (x y : A) (l : list A) : 
	path _ (split A (cons x (cons y l))) (cons x ((split A l).fst), cons y ((split A l).snd))
	= 
	let n = length A l in
	let p = symm _ (split/aux/suc A n l (le/refl n)) in
	λ i → (cons x ((p i).fst), cons y ((p i).snd))
	
def split/half (A : type) : (n : nat) → (l : list A) → (le (length A l) (double/nat n))
	→ 
	let s = split A l in 
	(le (length A (s.fst)) n) × 
	(le (length A (s.snd)) n) = 
	elim [
	| zero → 
		elim [
		| nil → λ _ → (★,★)
		| cons x xs → elim []
		]
	| suc (n → f) → 
		elim [
		| nil → λ _ → (★,★)
		| cons x xs → 
			elim xs [
			| nil → λ _ → (★,★)
			| cons y ys → λ p → 
				let p' : le (length A ys) (double/nat n) = p in
				let g = f ys p in 
				let p1 : le (length A ((split A ys).fst)) n = g.fst in 
				let p2 = g.snd in 
				let c1 = le/suc (length A ((split A ys).fst)) n p1 in
				let c2 = le/suc (length A ((split A ys).snd)) n p2 in 
				let p3 = split/cons/cons A x y ys in 
				coe 1 0 (c1,c2) in λ i → 
					let s = p3 i in 
					(le (length A (p3 i .fst)) (suc n)) × 
					(le (length A (p3 i .snd)) (suc n)) 
			]
		]
	]

quit
def msort (A : type) (ord : total/order A) : (n : nat) → list A → list A =
	elim [
	| zero → λ l → l
	| suc (n → f) → 
		elim [
		| nil → nil
		| cons x xs → 
			elim xs [
			| nil → cons x nil
			| cons y ys → 
				let s = split A (cons x (cons y ys)) in
				let p1 = s.fst in 
				let p2 = s.snd in 
				merge A ord (f p1) (f p2)
			]
		]
	]

def msort/nil (A : type) (ord : total/order A) : (n : nat) → 
	path _ (msort A ord n nil) nil = 
	elim [
	| zero → refl
	| suc n → refl
	]

def msort/single (A : type) (ord : total/order A) (x : A) : (n : nat) → 
	path _ (msort A ord n (cons x nil)) (cons x nil) = 
	elim [
	| zero → refl
	| suc n → refl
	]

def msort/fold (A : type) (ord : total/order A) : (l : list A) → (n : nat) → 
	path _ (merge A ord (msort A ord n ((split A l).fst)) (msort A ord n ((split A l).snd)))
	(msort A ord (suc n) l) = 
	elim [
	| nil → λ n → coe 1 0 refl in λ i → 
		path _ (merge A ord (msort/nil A ord n i) (msort/nil A ord n i)) nil
	| cons x xs → λ n → 
		elim xs [
		| nil → coe 1 0 refl in λ i → 
			path _ (merge A ord (msort/single A ord x n i) (msort/nil A ord n i)) (cons x nil)
		| cons y ys → refl
		]
	]

/-
def test (A : type) (ord : total/order A) (n : nat) (x y : A) (l : list A) : 
path _ (msort A ord (suc n) (cons x (cons y l))) 
	(merge A ord (msort A ord n ((split A (cons x (cons y l))).fst)) 
(msort A ord n ((split A (cons x (cons y l))).snd))) = refl
-/

def test = let p = split/half in p 

def msort/≅/sort (A : type) (ord : total/order A) : (n : nat) → (l : list A) →
	le (length A l) (pow2 n) → 
	path _ (sort A ord l) (msort A ord n l) = 
					let uu = split/half A in 
	elim [
	| zero → ?
	| suc (n → f) → 
		let P : (list A) → type = λ l → le (length A l) (pow2 (suc n)) → 
			path _ (sort A ord l) (msort A ord (suc n) l) in 
		let g0 : (l : list A) → le (length A l) zero → P l = 
			elim [
			| nil → λ _ _ → refl
			| cons x xs → λ p _ → 
				let p1 = le/zero/implies/zero (length A (cons x xs)) p in
				elim (zero/ne/suc (length A xs) p1) []
			] in
		let g1 : (l : list A) → le (length A l) (suc zero) → P l = 
			elim [
			| nil → λ _ _ → refl
			| cons x xs → 
				elim xs [
				| nil → λ _ _ → refl
				| cons y ys → λ p _ → 
				let p1 = le/pred (suc (length A ys)) zero p in 
				let p2 = le/zero/implies/zero (length A (cons y ys)) p1 in
				elim (zero/ne/suc (length A ys) p2) []
				]
			] in
		let g : (m : nat) → (l : list A) → le (length A l) m → P l = 
		elim [
		| zero → g0
		| suc (m → f1) → 
			elim m [
			| zero → g1
			| suc m' → 
				elim [
				| nil → λ _ _ → refl
				| cons x xs → 
					elim xs [
					| nil → λ _ _ → refl
					| cons y ys → λ p q → 
						/-
						let p1 = le/pred (suc (length A ys)) (suc m') p in 
						let p2 = le/pred (length A ys) m' p1 in 
						let p3 = le/suc/right (length A ys) m' p2 in 
						let p4 = le/pred/left (suc (length A ys)) (pow2 (suc n)) q in 
						let p5 = le/pred/left (length A ys) (pow2 (suc n)) p4 in 
						let p6 : path nat (suc m') m = refl in
						let p7 = f1 ys (coe 0 1 p3 in λ i → le (length A ys) (p6 i)) p5 in 
						-/
						let t : let s = split A (cons x (cons y ys)) in 
							(le (length A (s.fst)) (pow2 n))
						×	(le (length A (s.snd)) (pow2 n)) = ? in 
						let p8 = f ((split A (cons x (cons y ys))).fst) (t.fst) in 
							


						?
						/-
						let l : list A = cons x (cons y ys) in 
						let g : (l : list A) → le (length A l) (pow2 n) → 
							path _ (sort A ord l) (msort A ord n l) = f in 
						let g1 : le (length A xs) (pow2 (suc n)) → 
							path _ (sort A ord xs) (msort A ord (suc n) xs) = f1 in
						let p1 : le (suc (length A ys)) (pow2 (suc n)) = 
							le/pred/left (suc (suc (length A ys))) (pow2 (suc n)) p in
						let p2 : le (length A ys) (pow2 (suc n)) = 
							le/pred/left (suc (length A ys)) (pow2 (suc n)) p1 in
						let t = f2 p1 in ?
						-/
						
					]
				]
			]
		] in
		λ l p → g (length A l) l (le/refl (length A l)) p 
	]

quit
def ex4 = mergesort nat ord/nat (double/nat n10) (cons n3 (cons n2 (cons zero nil)))

meta <: print normalize ex4 :>

quit
def concat/perm (A : type) (ord : total/order A) : (s t s' t' : list A) → 
	perm A ord s s' → perm A ord t t' → perm A ord (append A s t) (append A s' t') =
	elim [
	| nil → λ t s' t' p1 p2 → 
		let p3 = sort/nil A ord s' p1 in 
		coe 0 1 p2 in λ i → perm A ord t (append A (p3 i) t') 
	| cons x xs → ?
		
	]

quit
def merge/perm (A : type) (ord : total/order A) : (s t s' t' : list A) → 
	perm A r s s' → perm A r t t' → perm A r (merge A r s t) (merge A r s' t') =
	elim [
	| nil → λ t s' t' p1 p2 → 
		let p3 = sort/nil A r s' p1 in 
		let p4 : path _ (sort A r t') (sort A r (merge A r s' t')) =
			λ i → sort A r (merge A r (p3 i) t') in 
		trans _ p2 p4 
	| cons x (xs → f) → λ t s' t' p1 p2 → ?
	]

quit
def split : (l : list nat) → (s t : list nat) × nat = ?


