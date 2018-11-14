import prelude.path
import prelude.equivalence

def ptype : type^1 = (A : type) × A

def pmap (pA pB : ptype) : type =
  (f : pA.fst → pB.fst) × path _ (f (pA.snd)) (pB.snd)

def p→ (pA pB : ptype) : ptype =
  (pmap pA pB, λ _ → pB.snd, refl)

def pequiv (pA pB : ptype) : type =
  (f : pmap pA pB) × is-equiv (pA.fst) (pB.fst) (f.fst)
