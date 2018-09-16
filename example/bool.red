import path

data bool where
| tt
| ff

let not : bool → bool =
  λ [ tt → ff | ff → tt ]

let not∘not (x : bool) : _ =
  not (not x)

let not∘not/id/pt : (x : bool) → path _ (not∘not x) x =
  λ [ _ → refl ]

-- Dedicated to Bob ;-)
let shannon (A : type) (f : bool → A) : bool → A =
  λ [ tt → f tt | ff → f ff ]

let shannon/path (A : type) (f : bool → A) : path _ f (shannon A f) =
  funext _ _ f (shannon A f) (λ [ _ → refl ])
