import data.nat
import data.unit 
import data.void
import prelude
import data.or
import data.int
import data.bool
import cool.nats
import paths.bool

def tt/ne/ff : path bool tt ff → void =
	λ p → coe 0 1 ★ in λ i → bool-path/code tt (p i)

def le : nat → nat → type =
  elim [
  | zero → λ _ → unit
  | suc (m → f) →
    elim [
    | zero → void
    | suc n → f n
    ]
  ]

def le/bool : nat → nat → bool =
  elim [
  | zero → λ _ → tt
  | suc (m → f) →
    elim [
    | zero → ff
    | suc n → f n
    ]
  ]

def le/bool/l : (n m : nat) → le n m → path _ (le/bool n m) tt = 
	elim [
	| zero → λ _ _ → refl
	| suc (n → f) → 
		elim [
		| zero → λ p → elim p []
		| suc m → f m
		]
	]

def le/bool/r : (n m : nat) → path _ (le/bool n m) tt → le n m = 
	elim [
	| zero → λ _ _ → ★
	| suc (n → f) → 
		elim [
		| zero → λ p → elim (tt/ne/ff (symm _ p)) []
		| suc m → f m
		]
	]

def le/bool/pred : (n m : nat) → path _ (le/bool (suc n) (suc m)) tt → 
	path _ (le/bool n m) tt =
	elim [
		| zero → λ _ _ → refl
		| suc _ → λ _ l → l
		]

def le/pred : (n m : nat) → le (suc n) (suc m) → le n m =
	elim [
		| zero → λ _ _ → ★
		| suc _ → λ _ l → l
		]

def le/suc/right : (n m : nat) → le n m → le n (suc m) =
  elim [
  | zero → λ _ _ → ★
  | suc (n' → f) →
    elim [
    | zero → elim []
    | suc m' → λ l → f m' l
    ]
  ]

def le/pred/left : (n m : nat) → le (suc n) m → le n m =
  elim [
  | zero → λ _ _ → ★
  | suc (n' → f) →
    elim [
    | zero → elim []
    | suc m' → λ l → f m' l
    ]
  ]

def le/suc : (n m : nat) → le n m → le (suc n) (suc m) =
  elim [
  | zero → λ _ _ → ★
  | suc _ → λ _ l → l
  ]

def le/refl : (n : nat) → le n n =
  elim [
  | zero → ★
  | suc (_ → f) → f
  ]

def le/zero/implies/zero : (n : nat) → (le n zero) → path nat zero n =
  elim [
  | zero → λ _ → refl
  | suc n' → elim []
  ]

def le/case : (m n : nat) → (le n (suc m)) → or (path nat n (suc m)) (le n m) =
  elim [
  | zero →
    elim [
    | zero → λ _ → inr ★
    | suc n' →
      elim n' [
      | zero → λ _ → inl refl
      | suc _ → λ p → inr p
      ]
    ]
  | suc (m' → c) →
    elim [
    | zero → λ _ → inr ★
    | suc n' → λ p →
      elim (c n' p) [
      | inl p → inl (λ i → suc (p i))
      | inr l → inr (le/suc n' m' l)
      ]
    ]
  ]

def sub/le : (n m : nat) → le (sub n m) n =
  elim [
  | zero → λ _ → ★
  | suc (n' → f) → λ m → elim m [
    | zero → le/refl n'
    | suc m' → le/suc/right (sub n' m') n' (f m')
    ]
  ]

def sub/zero/id (n : nat) : path _ (sub n zero) n = 
  elim n [
  | zero → refl
  | suc n' → refl
  ]

def sub/zero/zero/eq (n : nat) 
  : (m : nat) → path _ (sub n m) zero → path _ (sub m n) zero → path _ n m =
  elim n [
  | zero → λ m p1 p2 → trans _ (symm _ p2) (sub/zero/id m)
  | suc (n' → f) → elim [
    | zero → λ p _ → p
    | suc m' → λ p1 p2 → λ i → suc (f m' p1 p2 i)
    ] 
  ]

def sub/le/implies/le : (m n k : nat) → path nat (suc k) (sub m n) → le n m =
  elim [
  | zero →
    elim [
    | zero → λ _ _ → ★
    | suc n' → λ _ p → coe 1 0 ★ in λ i → le (p i) zero
    ]
  | suc (m' → f) →
    elim [
    | zero → λ _ _ → ★
    | suc n' → f n'
    ]
  ]

/- where's the hole?

def eq/sub/zero : (m n : nat) → path nat m n → path nat (sub m n) zero =
  elim [
  | zero → refl
	| suc (m' → f) → 
    elim [
    | zero → refl
    | suc n' → λ p → 
      let p' : path nat m' n' = λ i → nat-pred (p i) in
			f n' p'
    ]
  ]
-/

def path/implies/le (p : dim → nat) : le (p 0) (p 1) =
  coe 0 1 (le/refl (p 0)) in (λ i → le (p 0) (p i))

def sub/plus/path : (m n : nat) → le n m → path nat (plus n (sub m n)) m =
  elim [
  | zero → λ n p →
    let path/n/0 = symm nat (le/zero/implies/zero n p) in
    trans nat (eta n) path/n/0
  | suc (m' → f) → elim [
    | zero → refl
    | suc n' → λ p i → suc ((f n' p) i)
    ]
  ]

def plus/le : (m n : nat) → le m (plus m n) =
  elim [
  | zero → λ _ → ★
  | suc (m' → f) → f
  ]

def le/trans : (m n l : nat) → le m n → le n l → le m l =
  elim [
  | zero → λ _ _ _ _ → ★
  | suc (m' → f) →
    elim [
    | zero → λ _ → elim []
    | suc n' →
      elim [
      | zero → λ _ → elim []
      | suc l' → f n' l'
      ]
    ]
  ]

def plus/rinv/sub : (m n k : nat) → path nat k (sub m n) → le n m → path nat (plus k n) m =
  elim [
  | zero → 
    elim [
    | zero → λ k p _ → trans _ (eta k) p
    | suc n' → λ _ _ p → elim p []
    ]
  | suc (m' → f) → 
    elim [
    | zero → λ k p _ → trans _ (eta k) p
    | suc n' → λ k p l → 
      let p' : path nat (suc (plus k n')) (suc m') = λ i → suc (f n' k p l i) in
      trans _ (plus/suc/r k n') p' 
    ]
  ]

def izero : int = pos zero

def iplus/unit-r : (n : int) → path int (iplus n izero) n =
  elim [
  | pos n →
    elim n [
    | zero → refl
    | suc (n → n+0) → λ i → isuc (n+0 i)
    ]
  | negsuc n →
    elim n [
    | zero → refl
    | suc (n → n+0) → λ i → pred (n+0 i)
    ]
  ]

def iplus/unit-l : (n : int) → path int (iplus izero n) n =
  elim [
  | pos n →
    elim n [
    | zero → refl
    | suc (n → n+0) → λ i → isuc (n+0 i)
    ]
  | negsuc n →
    elim n [
    | zero → refl
    | suc (n → n+0) → λ i → pred (n+0 i)
    ]
  ]

def imult/zero-r : (n : int) → path int (imult n izero) izero =
	elim [
	| pos n → 
		elim n [
		| zero → refl
		| suc (n → p) → p
		]
	| negsuc n → refl
	]

def imult/zero-l : (n : int) → path int (imult izero n) izero = 
	elim [
	| pos n → refl
	| negsuc n → refl
	]

def imult/unit-l : (n : int) → path int (imult (pos (suc zero)) n) n = 
	elim [
	| pos n → λ i → pos ((eta n) i)
	| negsuc n → λ i → negsuc ((eta n) i)
	]

def zero/ne/suc : (n : nat) → path nat zero (suc n) → void = 
	λ n p → coe 0 1 ★ in λ i → le (p i) zero

def const/id (n : nat) (p : [i] nat [i=0 → n]) : nat = 
	elim n [
	| zero → zero 
	| suc _ → p 1
	]

def const/path (n : nat) : (p : [i] nat [i=0 → n]) → path nat n (const/id n p) = 	
	elim n [
	| zero → λ _ → refl
	| suc n → λ p → p
	]
	
def n1 : nat = suc zero
def n2 : nat = double/nat n1
def n3 : nat = suc n2
def n4 : nat = double/nat n2
def n5 : nat = suc n4
def n6 : nat = plus n2 n4
def n7 : nat = suc n6
def n8 : nat = double/nat n4
def n9 : nat = suc n8
def n10 : nat = double/nat n5
def n16 : nat = double/nat n8

quit
def imult/comm : (n m : int) → path int (iplus n m) (iplus m n) = 
	elim [
	| pos n → 
		elim n [
		| zero → λ m → symm _ (iplus/unit-r m)
		| suc n → ?
		]
	| negsuc n → ?
	]
