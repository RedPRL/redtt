import prelude
import cool.complete-induction
import data.nat
import data.void

def double : nat → nat =
  elim [
  | zero → zero
  | suc (n' → f) → suc (suc f)
  ]

def sub : nat → nat → nat =
  elim [
  | zero → λ _ → zero
  | suc (m' → sub/m') →
    elim [
    | zero → suc m'
    | suc n' → sub/m' n'
    ]
  ]

def sub/le : (n m : nat) → le (sub n m) n =
  elim [
  | zero → λ _ → triv
  | suc (n' → f) → λ m → elim m [
    | zero → le/refl n'
    | suc m' → le/suc/right (sub n' m') n' (f m')
    ]
  ]

def mod/prop : nat → type = λ _ → nat → nat

def mod : (n : nat) → mod/prop n =
  let complete = weak/implies/complete mod/prop (λ P → realize/weak/induction P) in
  complete
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
    )

def id/nat : nat → nat =
  elim [
  | zero → zero
  | suc (n' → f) → suc f
  ]

def eta : (n : nat) → path nat (id/nat n) n =
  elim [
  | zero → refl
  | suc (n' → p) → λ i → suc (p i)
  ]

def sub/plus/path : (m n : nat) → le n m → path nat (plus n (sub m n)) m =
  elim [
  | zero → λ n p →
    let path/n/0 = symm nat (le/zero/implies/zero n p) in
    trans nat (eta n) path/n/0
  | suc (m' → f) → elim [
    | zero → refl
    | suc n' → λ p → λ i → suc ((f n' p) i)
    ]
  ]

def plus/le : (m n : nat) → le m (plus m n) =
  elim [
  | zero → λ _ → triv
  | suc (m' → f) → f
  ]

def le/trans : (m n l : nat) → le m n → le n l → le m l =
  elim [
  | zero → λ _ _ _ _ → triv
  | suc (m' → f) → elim [
    | zero → λ l m'/le/n n/le/l → elim m'/le/n []
    | suc n' → elim [
      | zero → λ _ n/le/l → elim n/le/l []
      | suc l' → f n' l'
      ]
    ]
  ]

def sub/le/implies/le : (m n k : nat) → path nat (suc k) (sub m n) → le n m =
  elim [
  | zero →
    elim [
    | zero → λ _ _ → triv
    | suc n' → λ _ p → coe 1 0 triv in λ i → le (p i) zero
    ]
  | suc (m' → f) →
    elim [
    | zero → λ _ _ → triv
    | suc n' → f n'
    ]
  ]

def suc/right/path : (m n : nat) → path nat (plus (suc m) n) (plus m (suc n)) =
  elim [
  | zero → refl
  | suc (m' → f) → λ n i → suc (f n i)
  ]

def path/implies/le (p : dim → nat) : le (p 0) (p 1) =
  coe 0 1 (le/refl (p 0)) in (λ i → le (p 0) (p i))

def gcd/prop : nat → type = λ m → (x y : nat) → le (plus x y) m → nat

def gcd' : (m : nat) → gcd/prop m =
  let complete = weak/implies/complete gcd/prop (λ P → realize/weak/induction P) in
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
                let x/le/x+y' = coe 0 1 (plus/le (suc x') y') in 
                  λ i → le (suc x') (suc/right/path x' y' i)
                in
                let x/le/m = le/trans (suc x') (plus x' (suc y')) m x/le/x+y' x+y'/le/m in
                let g = sub/le/implies/le x' y' k' eq  in
                let h = sub/plus/path x' y' g in
                let i : le (plus (suc y') (sub x' y')) (suc x') = path/implies/le h in
                let b = f (suc x') x/le/m (suc y') (sub x' y') i  in
                b
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
                let b = f (suc y') y/le/m (suc x') (sub y' x') i  in
                b
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
def n8 : nat = double n4
def ex1 : nat = gcd n6 n8
def check/ex1 : path nat ex1 n2 = refl
def ex2 : nat = mod n8 n5
def check/ex2 : path nat ex2 n3 = refl
