import prelude 

def pullback (A B C : type) (f : A → C) (g : B → C) : type =
  (a : _) × (b : _) × path _ (f a) (g b)

def comm-square (P A B C : type) : type = 
  (f : A → C) × (g : B → C) × (h : P → A) × (k : P → B) × path (P → C) (λ x → f (h x)) (λ x → g (k x)) 

def pullback→comm (A B C : type) (f : A → C) (g : B → C) : comm-square (pullback A B C f g) A B C = 
  (f, g, λ p → p.fst, λ p → p.snd.fst, λ i p → p.snd.snd i)

def comm→pullback (P A B C : type) (sq : comm-square P A B C) : pullback (P → A) (P → B) (P → C) (λ pa p → sq.fst (pa p)) (λ pb p → sq.snd.fst (pb p)) = 
  let (f, g, h, k, p) = sq in
  (h, k, p)

def induced (X P A B C : type) (sq : comm-square P A B C) : (X → P) → pullback (X → A) (X → B) (X → C) (λ xa x → sq.fst (xa x)) (λ xb x → sq.snd.fst (xb x)) = 
  λ xp → 
    let (f, g, h, k, p) = sq in
    (λ x → h (xp x), λ x → k (xp x), λ i x → p i (xp x)) 

def is-pullback-square (P A B C : type) (sq : comm-square P A B C) : type^1 = 
  (X : type) → is-equiv _ _ (induced X P A B C sq)
 
def pullback/corner (A B C : type) (f : A → C) (g : B → C) : is-pullback-square (pullback _ _ _ f g) A B C (pullback→comm _ _ _ f g) = 
  λ X pbx → 
  let (h,k,p) = pbx in
  (
   ((λ x → (h x, k x, λ i → p i x)), refl), 
   λ d i → 
    let d2 = d.snd in
    (λ x → ((d2 i).fst x, (d2 i).snd.fst x, λ j → (d2 i).snd.snd j x), 
     λ j → connection/or _ d2 i j)
   )