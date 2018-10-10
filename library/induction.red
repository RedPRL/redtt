import bool
import nat
import path
import unit

def transport (A : type) (M N : A) (p : path A M N) (C : A → type) : C M → C N = 
	λ cm → coe 0 1 cm in λ i →  C (p i)

def le : nat →  nat →  type = 
	elim [
		|	zero →  λ _ →  unit
		| suc (m' → f) → 
		elim [
		| zero →  void
		| suc n' →  f n'
		]
	]

def le/suc (n: nat) : (m : nat) →  le n m → le (suc n) (suc m) =
	elim n [
	| zero →  \ _ _  →  triv
	| suc n' →  \ m' l → l 
	]

def eq/implies/le (n : nat) : le n n = 
	elim n [
		| zero →  triv
		| suc (n' →  f) →  f
	]

def le/zero/implies/zero (n : nat) : (le n zero) →  path nat zero n = 
	elim n [
		| zero →  \ _ →  refl
		| suc n' →  \ p →  elim p []
	]

def inc : nat → nat = (\ i →  suc i)

def le/case (m : nat) : (n : nat) → (le n (suc m)) →  or (path nat n (suc m)) (le n m) = 
	elim m [
		| zero →  \ n → 
			elim n [
				| zero →  \ _ →  inr triv
				| suc n' →  elim n' [
					| zero → \ _ →  inl refl
					| suc _ →  \ p →  inr p
				]
			]
		| suc (m' →  c) →  elim [
				| zero →  \ _ →  inr triv
				| suc n' →  \ p →  
				let r : or (path nat n' (suc m')) (le n' m') = c n' p in 
					elim r [
						| inl p →  inl (\i -> inc (p i))
						| inr l →  inr (le/suc n' m' l)
					]
			]
	]


def weak/induction (P : nat →  type)
: type = 	(P zero) →  ((n : nat) →  P n →  P (suc n)) →  ((n : nat) → P n)  

def complete/induction (P : nat →  type) : type =
	(P zero) →  ((n : nat) →  ((k : nat) → (le k n) →  P k) → P (suc n)) →  ((n : nat) → P n)  

def complete/implies/weak (P : nat →  type) : complete/induction P → weak/induction P = 
	λ complete p0 ps →  complete p0 (\ n f →  ps n (f n (eq/implies/le n)))

def weak/implies/complete : (P : nat → type) →  
	((P' : nat →  type) →  weak/induction P') →  complete/induction P = 
	λ P weak p0 ps →  
		let P' : nat → type = \n → (k : nat) → (le k n) →  P k in
		let P'0 : P' zero = \ k k/le/0 →  transport nat zero k (le/zero/implies/zero k k/le/0) P p0  in 
		let f : (n : nat) →  (P' n) → (P' (suc n)) = 
			\ n p'n →  \ k k/le/sn →  
			elim
			(le/case n k k/le/sn) [
				| inl p →  transport nat (suc n) k (symm nat p) P (ps n p'n)
				| inr l →  p'n k l
			]
		 in 
		 let P'n : ((n : nat) → P' n) = (weak P') P'0 f in
		 λ n →  P'n n n (eq/implies/le n)

