import prelude.path
import prelude.equivalence

def ptype : type^1 = (A : type) × A

def pmap (pA pB : ptype) : type =
  (f : pA.fst → pB.fst) × path _ (f (pA.snd)) (pB.snd)

def pidf (X : ptype) : pmap X X = (λ a → a, refl)

def p∘ (X Y Z : ptype) (g : pmap Y Z) (f : pmap X Y) : pmap X Z =
  (λ a → g .fst (f .fst a), trans (Z .fst) (λ i → g .fst (f .snd i)) (g .snd))

def p→ (pA pB : ptype) : ptype =
  (pmap pA pB, λ _ → pB.snd, refl)

def pequiv (pA pB : ptype) : type =
  (f : pmap pA pB) × is-equiv (pA.fst) (pB.fst) (f.fst)
