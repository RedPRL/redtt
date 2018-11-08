import prelude

data nat where
| zero
| suc (x : nat)

def nat-pred : nat → nat =
  elim [
  | zero → zero
  | suc n → n
  ]

def nat-pred/suc (x : nat) : path nat x (nat-pred (suc x)) =
  refl

def plus (m n : nat) : nat =
  elim m [
  | zero → n
  | suc (m → plus/m/n) → suc plus/m/n
  ]

def plus/unit/l (n : nat) : path nat (plus zero n) n =
  refl

def plus/unit/r : (n : nat) → path nat (plus n zero) n =
  elim [
  | zero → refl
  | suc (n → path/n) → λ i → suc (path/n i)
  ]

def plus/assoc : (n m o : nat) → path nat (plus n (plus m o)) (plus (plus n m) o) =
  elim [
  | zero → refl
  | suc (n → plus/assoc/n) → λ m o i → suc (plus/assoc/n m o i)
  ]

def plus/suc/r : (n m : nat) → path nat (plus n (suc m)) (suc (plus n m)) =
  elim [
  | zero → refl
  | suc (n → plus/n/suc/r) → λ m i → suc (plus/n/suc/r m i)
  ]


def plus/comm : (m n : nat) → path nat (plus n m) (plus m n) =
  elim [
  | zero → plus/unit/r
  | suc (m → plus/comm/m) → λ n → trans _ (plus/suc/r n m) (λ i → suc (plus/comm/m n i))
  ]

def id/nat : nat → nat =
  elim [
  | zero → zero
  | suc (_ → f) → suc f
  ]

def eta : (n : nat) → path nat (id/nat n) n =
  elim [
  | zero → refl
  | suc (_ → p) → λ i → suc (p i)
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

def mult (m n : nat) : nat = 
	elim m [
	| zero → zero 
	| suc (m' → mult/m'/n) → plus n mult/m'/n
	]

def mult/unit/l (n : nat) : path nat (mult (suc zero) n) n = eta n
