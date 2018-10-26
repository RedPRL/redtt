import prelude
import data.void
import data.unit
import data.bool
import basics.isotoequiv

def bool-path/code : bool → bool → type =
  elim [
  | tt → elim [
    | tt → unit
    | ff → void
    ]
  | ff → elim [
    | tt → void
    | ff → unit
    ]
  ]

def bool-refl : (x : bool) → bool-path/code x x =
  elim [
  | tt → triv
  | ff → triv
  ]  

def bool-path/encode (x y : bool) (p : path bool x y) : bool-path/code x y =
  coe 0 1 (bool-refl x) in λ i → bool-path/code x (p i)  

def not/neg : (x : bool) → neg (path bool (not x) x) = 
  elim [ 
   | tt → bool-path/encode ff tt 
   | ff → bool-path/encode tt ff 
  ]

def not/equiv : equiv bool bool =
  iso→equiv _ _ (not, (not, (not∘not/id/pt, not∘not/id/pt)))

def not/path : path^1 type bool bool =
  ua _ _ not/equiv
