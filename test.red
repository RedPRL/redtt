import path
import connection
import J

let id (X : type) (x : X) : _ = x

; demonstrate McBride-style account of uniform universe level shifting
let id_univ : type → type =
  id^1 _

let not (x : bool) : bool =
  if x then ff else tt

let not∘not (x : bool) : _ =
  not (not x)


let not∘not/id/pt (x : bool) : Path _ (not∘not x) x =
  if x then λ _ → tt else λ _ → ff


let not∘not/id : Path (bool → bool) not∘not (id _) =
  λ i x →
    not∘not/id/pt x i

let restriction-test : singleton bool tt = tt
let _ : restrict bool with 1=1 ⇒ tt end = restriction-test
let _ (M : singleton bool tt) : bool = M



let foo (x : bool × bool) : _ × _ =
  let z0 = x.0 in
  let z1 = x.1 in
  < z0, z1 >


let testing (x : restrict bool with 1=1 ⇒ tt end) : singleton bool tt =
  x

let hset (A : _) : type =
  (x, y : A)
  (p, q : Path A x y)
  → Path _ p q

let hset/pi
  (A : type)
  (B : A → type)
  (hset/B : (x : A) → hset (B x))
  : hset ((x : A) → B x)
  =
  λ f g α β i j x →
    hset/B _ (f x) (g x) (λ k → α k x) (λ k → β k x) i j


; this is an example that doesn't work so well in redprl-style sequent calculus
let theorem-of-choice
  (A, B : type)
  (R : A → B → type)
  (p : (x : A) → (y : B) × R x y)
  : (f : A → B) × (x : A) → R x (f x)
  =
  < λ x → p x .0
  , λ x → p x .1
  >
