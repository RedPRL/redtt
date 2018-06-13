import path
import connection

let not (x : bool) : bool =>
  if x then ff else tt

let not∘not (x : bool) : _ =>
  not (not x)


let not∘not/id/pt (x : bool) : Path bool (not∘not x) x =>
  if x then λ _ → tt else λ _ → ff


let not∘not/id : Path (bool → bool) _ _ =>
  λ i x →
    not∘not/id/pt x i



let restriction-test : singleton bool tt => _
let _ : `(bool [1=1 tt]) => restriction-test
let _ (M : singleton bool tt) : bool => M



let foo (x : bool × bool) : bool × bool =>
  let z0 => x.car in
  let z1 => x.cdr in
  < z0, z1 >


let testing (x : `(bool [1=1 tt])) : singleton bool tt =>
  x

let hset (A : _) : type =>
  (x : A)
  (y : A)
  (p : Path _ x y)
  (q : Path _ x y)
  → Path (Path A x y) p q

let hset/exponential-ideal
  (A : _)
  (B : _)
  (hset/B : hset B)
  : hset (A → B)
  =>
   λ f g α β i j x →
     hset/B _ _ (λ k → α k x) (λ k → β k x) i j

