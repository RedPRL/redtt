import prelude
import basics.retract

-- Half-adjoint equivalence

def lcoh (A B : type) (f : A → B) (g : B → A) (f-g : (b : _) → path _ (f (g b)) b) : type =
  (g-f : (a : _) → path _ (g (f a)) a)
  × (a : A) → path (path _ (f (g (f a))) (f a)) (λ i → f (g-f a i)) (f-g (f a))

def is-ha-equiv (A B : type) (f : A → B) : type =
  (g : B → A)
  × (f-g : (b : _) → path _ (f (g b)) b)
  × lcoh A B f g f-g

def ha-equiv (A B : type) : type = (f : A → B) × is-ha-equiv A B f

-- this symmetry function is exactly involutive on all but the highest coherence
def ha-equiv/symm (A B : type) (e : ha-equiv A B) : ha-equiv B A =
  let (f, g, f-g, g-f, adj) = e in
  let adj' (b : B) : path (path _ (g (f (g b))) (g b)) (λ i → g (f-g b i)) (g-f (g b)) =
    λ j i →
    let cap0 : A =
      comp 1 0 (g (f-g (f-g b i) j)) [
      | i=0 k → g (adj (g b) k j)
      | i=1 | ∂[j] → refl
      ]
    in
    let filler (x k : 𝕀) : A =
      comp 0 x (g-f (g b) k) [
      | k=0 x → g (f-g b x)
      | k=1 → refl
      ]
    in
    let cap1 : A =
      comp 0 1 cap0 [
      | i=0 k → g-f (g-f (g b) j) k
      | i=1 → filler j
      | j=0 k → g-f (g (f-g b i)) k
      | j=1 → filler i
      ]
    in
    comp 1 0 cap1 [
    | i=0 k → weak-connection/and A (g-f (g b)) j k
    | i=1 → refl
    | j=0 → refl
    | j=1 k → weak-connection/or A (g-f (g b)) i k
    ]
  in
  (g, f, g-f, f-g, adj')

def equiv→ha-equiv (A B : type) (e : equiv A B) : ha-equiv A B =
  let (f, c) = e in
  let g (b : B) = c b .fst .fst in
  let f-g (b : B) = c b .fst .snd in
  let p (a : A) = symm (fiber A B f (f a)) (c (f a) .snd (a, refl)) in
  ( f
  , g
  , f-g
  , λ a i → p a i .fst
  , λ a j i →
    comp 1 0 (p a i .snd j) [
    | i=0 k → weak-connection/and B (f-g (f a)) j k
    | i=1 → refl
    | j=0 → refl
    | j=1 k → weak-connection/or B (f-g (f a)) i k
    ]
  )
