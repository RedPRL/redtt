import prelude
import cool.complete-induction
import data.nat
import data.void
import data.unit
import data.int
import cool.nat-lemmas
import cool.div-mod

def double : nat → nat =
  elim [
  | zero → zero
  | suc (n' → f) → suc (suc f)
  ]

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

def path/implies/le (p : dim → nat) : le (p 0) (p 1) =
  coe 0 1 (le/refl (p 0)) in (λ i → le (p 0) (p i))

def min (A : nat → type) : type = (n : nat) × A n × (n' : nat) → A n → le n n' 

def positive (m : int) : type = 
  elim m [
  | pos m' → 
    elim m' [
    | zero → void
    | suc _ → unit
    ]
  | negsuc _ → void
  ]

def lift (m : int) : positive m → nat = 
  elim m [
  | pos m' → λ p → m'
  | negsuc _ → λ p → elim p []
  ]
  
def coeff (x y : nat) : nat → type = 
  λ n → 
  (k l : int) × 
  let d = iplus (imult k (pos x)) (imult l (pos y)) in (p : positive d) × path nat (lift d p) n 

def gcd/certify (x y d : nat) : type = 
  (s t : nat) 
  × path nat (mult s d) x × path nat (mult t d) y
  × (s' t' d' : nat) → path nat (mult s d) x × path nat (mult t d) y → le d d'

-- def bezout (x y : nat) (m : min (coeff x y)) : gcd/certify x y (m .fst) =  

def gcd/prop (m : nat) : type =
  (x y : nat) → le (plus x y) m → nat

def gcd' : (m : nat) → gcd/prop m =
  let complete = weak/implies/complete gcd/prop realize/weak/induction in
  complete
    (λ _ _ _ → zero)
    (λ m f → λ x y →
      elim x [
      | zero → λ _ → y
      | suc x' →
        elim y [
        | zero → λ _ → x
        | suc y' →
          elim (sub y x) [
          | zero → λ x+y'/le/m →
            let convoy : (k : nat) → path nat k (sub x' y') → nat =
              elim [
              | zero → λ _ → x
              | suc k' → λ eq →
                let x/le/x+y' =
                  coe 0 1 (plus/le (suc x') y') in
                  λ i → le (suc x') (symm _ (plus/suc/r x' y') i)
                in
                let x/le/m = le/trans (suc x') (plus x' (suc y')) m x/le/x+y' x+y'/le/m in
                let g = sub/le/implies/le x' y' k' eq  in
                let h = sub/plus/path x' y' g in
                let i : le (plus (suc y') (sub x' y')) (suc x') = path/implies/le h in
                f (suc x') x/le/m (suc y') (sub x' y') i
              ]
            in
            convoy (sub x' y') refl
          | suc _ → λ x'+y/le/m →
            let convoy : (k : nat) → path nat k (sub y' x') → nat =
              elim [
              | zero → λ _ → x
              | suc k' → λ eq →
                let y/le/x'+y = coe 0 1 (plus/le (suc y') x') in
                  λ i → le (suc y') (plus/comm x' (suc y') i)
                in
                let y/le/m = le/trans (suc y') (plus x' (suc y')) m y/le/x'+y x'+y/le/m in
                let g = sub/le/implies/le y' x' k' eq in
                let h = sub/plus/path y' x' g in
                let i : le (plus (suc x') (sub y' x')) (suc y') = path/implies/le h in
                f (suc y') y/le/m (suc x') (sub y' x') i
              ]
            in
            convoy (sub y' x') refl
          ]
        ]
      ]
    )

def gcd (m n : nat) : nat = gcd' (plus m n) m n (le/refl (plus m n))

def n1 : nat = suc zero
def n2 : nat = double n1
def n3 : nat = suc n2
def n4 : nat = double n2
def n5 : nat = suc n4
def n6 : nat = plus n2 n4
def n7 : nat = suc n6
def n8 : nat = double n4
def n16 : nat = double n8

def ex1 = gcd n6 n8
def ex2 = div-mod n8 n5
def ex3 = div-mod n16 n7
def check/ex1 : path nat ex1 n2 = refl
def check/ex2 : path (nat × nat) (ex2.fst,ex2.snd.fst) (n1,n3) = refl
def check/ex3 : path (nat × nat) (ex3.fst,ex3.snd.fst) (n2,n2) = refl
