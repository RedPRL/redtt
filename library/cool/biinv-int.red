import prelude
import data.nat
import data.int
import basics.isotoequiv
import basics.ha-equiv
import basics.retract

data biinv-int where
| zero
| suc (z : biinv-int)
| predl (z : biinv-int)
| predr (z : biinv-int)
| predl-suc (z : biinv-int) (i : 𝕀) [i=0 → predl (suc z) | i=1 → z]
| suc-predr (z : biinv-int) (i : 𝕀) [i=0 → suc (predr z) | i=1 → z]

def predl/ha-equiv : ha-equiv biinv-int biinv-int =
  equiv→ha-equiv _ _
    (iso→equiv biinv-int biinv-int
      ( λ z → predl z
      , λ z → suc z
      , λ z i → predl-suc z i
      , λ z i →
        comp 0 1 (suc (predl-suc (predr z) i)) [
        | i=0 j → suc (predl (suc-predr z j))
        | i=1 j → suc-predr z j
        ]
      ))

def suc-predl = predl/ha-equiv .snd .snd .snd .fst
def predl-adj = predl/ha-equiv .snd .snd .snd .snd
def suc-adj = ha-equiv/symm _ _ predl/ha-equiv .snd .snd .snd .snd

def suc/equiv : equiv biinv-int biinv-int =
  iso→equiv biinv-int biinv-int
    ( λ z → suc z
    , λ z → predl z
    , suc-predl
    , λ z i → predl-suc z i
    )

def predl~predr (z : biinv-int) : path biinv-int (predl z) (predr z) =
  λ j →
  equiv-section/prop biinv-int biinv-int (λ z → suc z) (suc/equiv .snd)
    (λ z → predl z, suc-predl)
    (λ z → predr z, λ z i → suc-predr z i)
    j .fst z

def suc-predl~suc-predr (z : biinv-int) : [j i] biinv-int [
  | i=0 → suc (predl~predr z j)
  | i=1 → z
  | j=0 → suc-predl z i
  | j=1 → suc-predr z i
  ]
  =
  λ j i →
  equiv-section/prop biinv-int biinv-int (λ z → suc z) (suc/equiv .snd)
    (λ z → predl z, suc-predl)
    (λ z → predr z, λ z i → suc-predr z i)
    j .snd z i

-- proof that biinv-int is equivalent to int

def fwd/pos : nat → biinv-int = elim [zero → zero | suc (_ → ih/n) → suc ih/n]

def fwd/negsuc : nat → biinv-int = elim [zero → predl zero | suc (_ → ih/n) → predl ih/n]

def fwd : int → biinv-int = elim [pos n → fwd/pos n | negsuc n → fwd/negsuc n]

def bwd : biinv-int → int =
  elim [
  | zero → pos zero
  | suc (z → ih/z) → isuc ih/z
  | predl (z → ih/z) → pred ih/z
  | predr (z → ih/z) → pred ih/z
  | predl-suc (z → ih/z) i → pred-isuc ih/z i
  | suc-predr (z → ih/z) i → isuc-pred ih/z i
  ]

def bwd-fwd/pos : (n : nat) → path _ (bwd (fwd/pos n)) (pos n) =
  elim [
  | zero → refl
  | suc (_ → n/ih) → λ k → isuc (n/ih k)
  ]

def bwd-fwd/negsuc : (n : nat) → path _ (bwd (fwd/negsuc n)) (negsuc n) =
  elim [
  | zero → refl
  | suc (_ → n/ih) → λ k → pred (n/ih k)
  ]

def bwd-fwd : (n : int) → path _ (bwd (fwd n)) n =
  elim [pos n → bwd-fwd/pos n | negsuc n → bwd-fwd/negsuc n]

def fwd/isuc/negsuc : (n : nat)
  → path _ (fwd (isuc (negsuc n))) (suc (fwd (negsuc n)))
  =
  elim [
  | zero → λ k → symm' biinv-int (λ j → suc-predl zero j) k
  | suc n → λ k → symm' biinv-int (λ j → suc-predl (fwd/negsuc n) j) k
  ]

def fwd/isuc : (n : int) → path _ (fwd (isuc n)) (suc (fwd n)) =
  elim [pos n → refl | negsuc n → fwd/isuc/negsuc n]

def fwd/pred/pos : (n : nat)
  → path _ (fwd (pred (pos n))) (predl (fwd/pos n))
  =
  elim [
  | zero → refl
  | suc n → λ k → symm' biinv-int (λ i → predl-suc (fwd/pos n) i) k
  ]

def fwd/pred : (n : int) → path _ (fwd (pred n)) (predl (fwd n)) =
  elim [pos n → fwd/pred/pos n | negsuc n → refl]


def fwd/pred-isuc/negsuc : (n : nat) → [i k] biinv-int [
  | i=0 → trans biinv-int (fwd/pred (isuc (negsuc n))) (λ k → predl (fwd/isuc/negsuc n k)) k
  | i=1 → fwd/negsuc n
  | k=0 → fwd (pred-isuc (negsuc n) i)
  | k=1 → predl-suc (fwd/negsuc n) i
  ]
  =
  elim [
  | zero → λ i k →
    comp 0 1 (predl (symm'/filler biinv-int (λ i → suc-predl zero i) i k)) [
    | i=0 m → trans/unit/l biinv-int (λ k → predl (fwd/isuc/negsuc zero k)) m k
    | i=1 | k=0 → refl
    | k=1 m → predl-adj zero m i
    ]
  | suc n → λ i k →
    comp 0 1 (predl (symm'/filler biinv-int (λ i → suc-predl (fwd/negsuc n) i) i k)) [
    | i=0 m → trans/unit/l biinv-int (λ k → predl (fwd/isuc/negsuc (suc n) k)) m k
    | i=1 | k=0 → refl
    | k=1 m → predl-adj (fwd/negsuc n) m i
    ]
  ]

def fwd/pred-isuc : (n : int) → [i k] biinv-int [
  | i=0 → trans biinv-int (fwd/pred (isuc n)) (λ k → predl (fwd/isuc n k)) k
  | i=1 → fwd n
  | k=0 → fwd (pred-isuc n i)
  | k=1 → predl-suc (fwd n) i
  ]
  =
  elim [
  | pos n → λ i k →
    comp 0 1 (symm'/filler biinv-int (λ i → predl-suc (fwd/pos n) i) i k) [
    | i=0 m → trans/unit/r biinv-int (fwd/pred/pos (suc n)) m k
    | i=1 | ∂[k] → refl
    ]
  | negsuc n → fwd/pred-isuc/negsuc n
  ]

def fwd/isuc-pred/pos : (n : nat) → [i k] biinv-int [
  | i=0 → trans biinv-int (fwd/isuc (pred (pos n))) (λ k → suc (fwd/pred/pos n k)) k
  | i=1 → fwd/pos n
  | k=0 → fwd (isuc-pred (pos n) i)
  | k=1 → suc-predl (fwd/pos n) i
  ]
  =
  elim [
  | zero → λ i k →
    comp 0 1 (symm'/filler biinv-int (λ i → suc-predl zero i) i k) [
    | i=0 m → trans/unit/r biinv-int (fwd/isuc/negsuc zero) m k
    | i=1 | ∂[k] → refl
    ]
  | suc n → λ i k →
    comp 0 1 (suc (symm'/filler biinv-int (λ i → predl-suc (fwd/pos n) i) i k)) [
    | i=0 m → trans/unit/l biinv-int (λ k → suc (fwd/pred/pos (suc n) k)) m k
    | i=1 | k=0 → refl
    | k=1 m → suc-adj (fwd/pos n) m i
    ]
  ]


def fwd/isuc-pred : (n : int) → [i k] biinv-int [
  | i=0 → trans biinv-int (fwd/isuc (pred n)) (λ k → suc (fwd/pred n k)) k
  | i=1 → fwd n
  | k=0 → fwd (isuc-pred n i)
  | k=1 → suc-predl (fwd n) i
  ]
  =
  elim [
  | pos n → fwd/isuc-pred/pos n
  | negsuc n → λ i k →
    comp 0 1 (symm'/filler biinv-int (λ i → suc-predl (fwd/negsuc n) i) i k) [
    | i=0 m → trans/unit/r biinv-int (fwd/isuc/negsuc (suc n)) m k
    | i=1 | ∂[k] → refl
    ]
  ]

def fwd-bwd : (z : biinv-int) → path _ (fwd (bwd z)) z =
  elim [
  | zero → refl
  | suc (z → z/ih) → trans biinv-int (fwd/isuc (bwd z)) (λ k → suc (z/ih k))
  | predl (z → z/ih) → trans biinv-int (fwd/pred (bwd z)) (λ k → predl (z/ih k))
  | predr (z → z/ih) → trans biinv-int (fwd/pred (bwd z)) (λ k → predl~predr (z/ih k) k)
  | predl-suc (z → z/ih) i → λ k →
    comp 0 1 (fwd/pred-isuc (bwd z) i k) [
    | i=0 m →
      trans biinv-int (fwd/pred (isuc (bwd z)))
        (λ k → predl (trans/filler biinv-int (fwd/isuc (bwd z)) (λ k → suc (z/ih k)) m k)) k
    | i=1 m → weak-connection/and biinv-int z/ih k m
    | k=0 → refl
    | k=1 m → predl-suc (z/ih m) i
    ]
  | suc-predr (z → z/ih) i → λ k →
    comp 0 1 (fwd/isuc-pred (bwd z) i k) [
    | i=0 m →
      trans biinv-int (fwd/isuc (pred (bwd z)))
        (λ k → suc (trans/filler biinv-int (fwd/pred (bwd z)) (λ k → predl~predr (z/ih k) k) m k)) k
    | i=1 m → weak-connection/and biinv-int z/ih k m
    | k=0 → refl
    | k=1 m → suc-predl~suc-predr (z/ih m) m i
    ]
  ]

def int-equiv-biinv-int : equiv int biinv-int =
  iso→equiv _ _ (fwd,bwd,fwd-bwd,bwd-fwd)
