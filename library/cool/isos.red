import prelude
import basics.isotoequiv
import data.unit
import data.void
import data.or

-- pair isos

def iso/pair/comm (A B : type) : iso (A × B) (B × A) = 
  ( λ (a,b) → (b,a)
  , λ (b,a) → (a,b)
  , λ _ → refl
  , λ _ → refl
  )

def iso/pair/assoc (A B C : type) : iso (A × B × C) ((A × B) × C) = 
  ( λ (a,b,c) → ((a,b),c)
  , λ ((a,b),c) → (a,b,c) 
  , λ _ → refl
  , λ _ → refl
  )

def iso/pair/unit (A : type) : iso (A × unit) A = 
  ( λ (a,_) → a
  , λ a → (a,★)
  , λ _ → refl
  , λ (a,u) i → (a, unit/prop ★ u i)
  )

def iso/pair/void (A : type) : iso (A × void) void = 
  ( λ (_,v) → exfalso _ v
  , λ v → exfalso _ v
  , λ v → exfalso _ v
  , λ (_,v) → exfalso _ v
  )

-- or isos

def iso/or/comm (A B : type) : iso (or A B) (or B A) = 
  ( elim [ inl a → inr a | inr b → inl b ]
  , elim [ inl b → inr b | inr a → inl a ]
  , elim [ inl _ → refl | inr _ → refl ]
  , elim [ inl _ → refl | inr _ → refl ]
  )

def iso/or/assoc (A B C : type) : iso (or A (or B C)) (or (or A B) C) = 
  ( elim [ inl a → inl (inl a) | inr bc → elim bc [ inl b → inl (inr b) | inr c → inr c ] ]
  , elim [ inl ab → elim ab [ inl a → inl a | inr b → inr (inl b) ] | inr c → inr (inr c) ]
  , elim [ inl ab → elim ab [ inl _ → refl | inr _ → refl ] | inr _ → refl ]
  , elim [ inl _ → refl | inr bc → elim bc [ inl _ → refl | inr _ → refl ] ]
  )

def iso/or/void (A : type) : iso (or A void) A = 
  ( elim [ inl a → a | inr v → exfalso _ v ]
  , λ a → inl a
  , λ _ → refl
  , elim [ inl _ → refl | inr v → exfalso _ v ]
  )

-- function isos

def curry (A B C : type) : ((A × B) → C) → (A → B → C) = 
  λ f a b → f (a, b)

def uncurry (A B C : type) : (A → B → C) → ((A × B) → C) = 
  λ f (a, b) → f a b

def iso/curry (A B C : type) : iso (A → B → C) ((A × B) → C) = 
  ( uncurry _ _ _
  , curry _ _ _
  , λ _ → refl
  , λ _ → refl
  )

def iso/lhs (A B C : type) (I : iso A B) : iso (A → C) (B → C) = 
  let (f,g,α,β) = I in
  ( λ ac b → ac (g b)
  , λ bc a → bc (f a)
  , λ bc i b → bc (α b i)
  , λ ac i a → ac (β a i)
  )

def iso/rhs (A B C : type) (I : iso A B) : iso (C → A) (C → B) = 
  let (f,g,α,β) = I in
  ( λ ca c → f (ca c)
  , λ cb c → g (cb c)
  , λ cb i c → α (cb c) i
  , λ ca i c → β (ca c) i
  )

def iso/flip (A B C : type) : iso (A → B → C) (B → A → C) = 
  ( λ f b a → f a b
  , λ f a b → f b a
  , λ _ → refl
  , λ _ → refl
  )

-- we can also compose the flip iso

def iso/flip/2 (A B C : type) : iso (A → B → C) (B → A → C) = 
  iso/trans _ _ _ (iso/curry A B C) 
    (iso/trans _ _ _ (iso/lhs (A × B) (B × A) C (iso/pair/comm A B)) 
                     (iso/symm _ _ (iso/curry B A C)))
