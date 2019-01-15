import prelude
import data.bool
import data.void
import cool.nat-lemmas

def total/order (A : type) : type = 
	(r : A → A → bool) × 
	((x y : A) → (path _ (r x y) (r y x) → path A x y))
	× ((x : A) → path _ (r x x) tt)
	× ((x y z : A) → path _ (r x y) tt → path _ (r y z) tt → path _ (r x z) tt)

def total/tt/ff (A : type) (ord : total/order A) (x y : A) : 
	path _ (ord.fst x y) ff → path _ (ord.fst y x) tt = 
	λ p → 
	let convoy : (b : bool) → path _ (ord.fst y x) b → path _ (ord.fst y x) tt = 
	elim [
	| tt → λ p → p
	| ff → λ p' → 
		let p1 = trans _ p (symm _ p') in 
		let p2 = ord.snd.fst x y p1 in 
		let p3 = coe 0 1 p in λ i → path _ (ord.fst (p2 i) y) ff in
		let p4 = ord.snd.snd.fst y in 
		elim (tt/ne/ff (trans _ (symm _ p4) p3)) []
	]
	in convoy (ord.fst y x) refl

def total/cycle (A : type) (ord : total/order A) (x y z : A) 
	(p1 : path _ (ord.fst x y) tt) 
	(p2 : path _ (ord.fst y z) tt) 
	(p3 : path _ (ord.fst z x) tt) : 
		(path _ x y)
	× (path _ x z) =
	let p4 = ord.snd.snd.snd x y z p1 p2 in 
	let p5 = ord.snd.fst x z (trans _ p4 (symm _ p3)) in 
	let p6 = coe 1 0 p2 in λ i → path _ (ord.fst y (p5 i)) tt in
	let p7 = ord.snd.fst x y (trans _ p1 (symm _ p6)) in 
	(p7,p5)

def total/ff/eq (A : type) (ord : total/order A) (x y : A)
	(p : path _ (ord.fst x y) ff) (q : path _ x y) : void =
	let p1 = coe 0 1 (ord.snd.snd.fst x) in λ i → path _ (ord.fst x (q i)) tt in 
	tt/ne/ff (trans _ (symm _ p1) p)
	
