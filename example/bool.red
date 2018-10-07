import path


data bool where
| tt
| ff

def not : bool → bool =
  elim [ tt → ff | ff → tt ]

def not∘not (x : bool) : _ =
  not (not x)

def not∘not/id/pt : (x : bool) → path _ (not∘not x) x =
  λ * → refl

-- Dedicated to Bob ;-)
def shannon (A : type) (f : bool → A) : bool → A =
  elim [ tt → f tt | ff → f ff ]

def shannon/path (A : type) (f : bool → A) : path _ f (shannon A f) =
  funext _ _ f (shannon A f) (λ * → refl)
