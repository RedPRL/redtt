import prelude
import cool.complete-induction
import data.nat
import data.void

def double : nat → nat = λ n →
  elim n [
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

def sub/le (n : nat) : (m : nat) → le (sub n m) n =
  elim n [
    | zero → λ _ → triv
    | suc (n' → f) → λ m → elim m [
      | zero → le/refl n'
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

def const/zero : nat → nat =
  elim [
    | zero → zero
    | suc (n' → f) → suc f
  ]

def eta : (n : nat) → path nat (const/zero n) n =
  elim [
    | zero → refl
    | suc (n' → p) → λ i → suc (p i)
  ]

def sub/plus/path (m : nat) : (n : nat) → le n m → path nat (plus n (sub m n)) m =
  elim m [
    | zero → λ n p →
      let path/n/0 = symm nat (le/zero/implies/zero n p) in
      trans nat (eta n) path/n/0
    | suc (m' → f) → elim [
      | zero → refl
      | suc n' → λ p → λ i → suc ((f n' p) i)
    ]

  ]

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

def sub/le/implies/le (m : nat) : (n k : nat) → path nat (suc k) (sub m n) → le n m =
  elim m [
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

def suc/right/path (m : nat) : (n : nat) → path nat (plus (suc m) n) (plus m (suc n)) =
  elim m [
    | zero → refl
    | suc (m' → f) → λ n i → suc (f n i)
  ]

def path/implies/le (m n : nat) : path nat m n → le m n =
  λ p → coe 0 1 (le/refl m) in (λ i → le (p 0) (p i))

def gcd/prop : nat → type = λ m → (x y : nat) → le (plus x y) m → nat

def gcd' (m : nat) : gcd/prop m =
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
                let x/le/x+y' : le (suc x') (plus x' (suc y')) =
                coe 0 1 (plus/le (suc x') y') in λ i → le (suc x')
                    (suc/right/path x' y' i) in
                let x/le/m = le/trans (suc x') (plus x' (suc y')) m x/le/x+y' x+y'/le/m in
                let g = sub/le/implies/le x' y' k' eq  in
                let h = sub/plus/path x' y' g in
                let i : le (plus (suc y') (sub x' y')) (suc x') = path/implies/le _ _ h in
                let b = f (suc x') x/le/m (suc y') (sub x' y') i  in
                b
              ] in convoy (sub x' y') refl

            | suc _ → λ x'+y/le/m →
              let convoy : (k : nat) → path nat k (sub y' x') → nat =
              elim [
                | zero → λ _ → x
                | suc k' → λ eq →
                let y/le/x'+y = coe 0 1 (plus/le (suc y') x') in λ i →
                                  le (suc y') (plus/comm x' (suc y') i) in
                let y/le/m = le/trans (suc y') (plus x' (suc y')) m y/le/x'+y x'+y/le/m in
                let g = sub/le/implies/le y' x' k' eq in
                let h = sub/plus/path y' x' g in
                let i : le (plus (suc x') (sub y' x')) (suc y') = path/implies/le _ _ h in
                let b = f (suc y') y/le/m (suc x') (sub y' x') i  in
                b
              ] in convoy (sub y' x') refl
            ]
        ]
    ]) m

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
