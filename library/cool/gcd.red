import prelude
import cool.complete-induction
import data.nat
import data.void


def double : nat → nat = λ n → 
  elim n [
    | zero → zero
    | suc (n' → f) → suc (suc f)  
  ]

def n1 : nat = suc zero
def n2 : nat = double n1
def n3 : nat = suc n2
def n4 : nat = double n2
def n5 : nat = suc n4
def n6 : nat = suc n5
def n7 : nat = suc n6
def n8 : nat = double n4
def n16 : nat = double n8 
def n32 : nat = double n16

def sub : nat → nat → nat = 
  elim [
    | zero → λ _ → zero 
    | suc (m' → sub/m') → 
    elim [
      | zero → suc m'
      | suc n' → sub/m' n'
    ]
  ]

def sub/le (n : nat) : (m : nat) → le (sub n m) n =
  elim n [
    | zero → λ _ → triv
    | suc (n' → f) → λ m → elim m [
      | zero → eq/implies/le n'
      | suc m' → le/suc/right (sub n' m') n' (f m')
    ]
   ]

def mod/prop : nat → type = λ n → nat → nat



def mod (n : nat) : mod/prop n =
  let complete = weak/implies/complete mod/prop (λ P → realize/weak/induction P) in
  let mod/code = complete 
  (λ _ → zero)
  (λ n f → λ m → 
    elim m [
      | zero → zero
      | suc m' → 
        elim (sub (suc n) m) [ 
          | zero → 
            elim (sub m (suc n)) [
              | zero → zero
              | suc _ → suc n
            ]
          | suc _ → (f (sub (suc n) (suc m')) (sub/le n m')) (suc m') 
        ] 
    ]
  ) in mod/code n


def sub/plus/path (m : nat) : (n : nat) → le n m → path nat (plus n (sub m n)) m = 
  elim m [
    | zero → λ n p → ?
    | suc (m' → f) → elim [
      | zero → refl
      | suc n' → λ p → λ i → suc ((f n' p) i)
    ]
      
  ]

quit

def plus/le (m : nat) : (n : nat) → le m (plus m n) = 
  elim m [
    | zero → λ _ → triv
    | suc (m' → f) → f
  ]

def le/trans (m : nat) : (n : nat) → (l : nat) → (le m n) → (le n l) → (le m l) =
  elim m [
    | zero → λ _ _ _ _ → triv
    | suc (m' → f) → λ n → elim n [
      | zero → λ l m'/le/n n/le/l → elim m'/le/n []
      | suc n' → elim [
        | zero → λ _ n/le/l → elim n/le/l []
        | suc l' → f n' l'
      ]
    ]
  ]

def sub/le/implies/le (m : nat) : (n : nat) → path nat (suc zero) (sub m n) → le n m = 
  elim m [
    | zero → 
      elim [
        | zero → λ _ → triv
        | suc n' → λ p → coe 1 0 triv in λ i → le (p i) zero
      ]
    | suc (m' → f) → 
      elim [
        | zero → λ _ → triv
        | suc n' → f n' 
      ]
  ]

def suc/right/path (m : nat) : (n : nat) → path nat (plus (suc m) n) (plus m (suc n)) =
  elim m [
    | zero → refl
    | suc (m' → f) → λ n i → suc (f n i)
  ]

def path/implies/le (m n : nat) : path nat m n → le m n = 
  λ p → coe 0 1 (eq/implies/le m) in (λ i → le (p 0) (p i))

def gcd/prop : nat → type = λ m → (x y : nat) → le (plus x y) m → nat

def gcd (m : nat) : gcd/prop m = 
  let complete : complete/induction gcd/prop 
    = weak/implies/complete gcd/prop (λ P → realize/weak/induction P) in
  let gcd/code = complete
  (λ _ _ _ → zero)
  (λ m f → λ x y →
    elim x [
      | zero → λ _ → y 
      | suc x' → 
        elim y [
          | zero → λ _ → x
          | suc y' → 
            elim (sub y x) [
            | zero → 
              elim (sub x y) [
              | zero → λ _ → x 
              | suc _ → λ x+y'/le/m → 
                let _ : le (plus x' (suc y')) m = x+y'/le/m in
                let x/le/x+y' : le (suc x') (plus x' (suc y')) = 
                coe 0 1 (plus/le (suc x') y') in λ i → le (suc x') 
                    (suc/right/path x' y' i) in 
                let x/le/m = le/trans (suc x') (plus x' (suc y')) m x/le/x+y' x+y'/le/m in
                let g = sub/le/implies/le x' y' refl in 
                let h = sub/plus/path x' y' g in 
                let i : le (plus (suc y') (sub x' y')) (suc x') = path/implies/le _ _ h in
                let b = f (suc x') x/le/m (suc y') (sub x' y') i  in 
                b
              ]

            | suc _ → λ x'+y/le/m →   
              let y/le/x'+y = coe 0 1 (plus/le (suc y') x') in λ i → 
                                le (suc y') (plus/comm x' (suc y') i) in 
              let y/le/m = le/trans (suc y') (plus x' (suc y')) m y/le/x'+y x'+y/le/m in
              let g = sub/le/implies/le y' x' refl in 
              let h = sub/plus/path y' x' g in 
              let i : le (plus (suc x') (sub y' x')) (suc y') = path/implies/le _ _ h in
              let b = f (suc y') y/le/m (suc x') (sub y' x') i  in 
              b
          ]
        ]
    ] 

   )
  in 
  gcd/code m
  
def ex : nat = gcd (plus n16 n4) n4 n8 triv

meta <: debug unsolved :>
