import prelude
import cool.complete-induction 
import cool.nat-lemmas 
import data.nat

def div-mod/prop : nat → type = 
  λ x → (y : nat) → (q : nat) × (r : nat) × path _ (plus (mult q y) r) x

def div-mod : (n : nat) → div-mod/prop n =
  let complete = weak/implies/complete div-mod/prop (λ P → realize/weak/induction P) in
  complete
    (λ _ → (zero,zero,refl))
    (λ n f → λ m → 
      elim m [
      | zero → (zero,suc n,refl)
      | suc m' → 
	let convoy : (k1 k2 : nat) → path _ (sub (suc n) (suc m')) k1 → 
	  path _ (sub (suc m') (suc n)) k2 → (q : nat) × (r : nat) 
	  × path nat (plus (mult q (suc m')) r) (suc n) 
	= λ k1 k2 → 
	elim k1 [
        | zero →
          elim k2 [
          | zero → λ p1 p2 → 
	    let g = trans _ (plus/unit/r (mult (suc zero) (suc m'))) 
	      (mult/unit/l (suc m')) in 
	    let h = sub/zero/zero/eq (suc m') (suc n) p2 p1 in
	     (suc zero,zero,trans _ g h)
          | suc _ → λ _ _ → (zero,suc n,refl)
          ]
        | suc d → λ p _ → 
	let g = f (sub (suc n) (suc m')) (sub/le n m') (suc m') in 
	let q = g.fst in 
	let q' : nat = suc (g.fst) in 
	let r = g.snd.fst in 
	let e = g.snd.snd in 
	let m'/le/n = sub/le/implies/le n m' d (symm _ p) in
	let e1 : path nat (plus (e 0) m') n = plus/rinv/sub n m' (e 0) e m'/le/n in 
	let e2 : path nat (suc (e1 0)) (suc (e1 1)) = λ i → suc (e1 i) in
	let e3 = trans _ (plus/suc/r (e 0) m') e2 in 
	let e4 = trans _ (plus/comm (e 0) (suc m')) e3 in 
	let e5 = trans _ (symm _ (plus/assoc (suc m') (mult q (suc m')) r)) e4 in 
	(q',r,e5)
	]
	in convoy (sub (suc n) (suc m')) (sub (suc m') (suc n)) refl refl
      ]
  )

def aux : nat → nat → nat → nat → (nat × nat) = 
	elim [
	| zero → λ _ _ q → (q,zero)
	| suc (x' → f) → 
		elim [
		| zero → λ _ _ → (zero,suc x')
		| suc y' → 
			λ r → 
			let d : nat = sub (suc x') r in
			let k = sub (suc y') d in 
			let l = sub d (suc y') in 
				elim k [
				| zero → 
					elim l [
					| zero → λ q → (suc q,zero)
					| suc _ → λ q → f (suc y') (plus y' r) (suc q)
					]
				| suc _ → λ q → (q,d)
				]
		]
	]

def div-mod' : nat → nat → (nat × nat) = 
	λ x y → aux x y zero zero 
