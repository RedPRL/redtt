import path


let not [x : `bool] : _ ⇒
  `(if [_] bool x ff tt)

let id [A : type] [x : A] : A ⇒
  x

let not∘not [x : `bool] : _ ⇒
 `(not (not x))


let not∘not/id/pt [x : `bool] : _ ⇒
 `(if
   [x] (Path bool (not∘not x) x)
   x
   (λ <i> tt)
   (λ <i> ff))

let not∘not/id : Path `(→ bool bool) _ _ ⇒
  λ i x →
   `(@ (not∘not/id/pt x) i)


let singleton [A : type] [M : A] : `(U pre 0) ⇒
  `(A [0=0 M])

let restriction-test : singleton `bool `tt ⇒ _
let _ : `(bool [1=1 tt]) ⇒ restriction-test
let _ [M : singleton `bool `tt] : `bool ⇒ M



let foo [x : `(× bool bool)] : `(× bool bool) ⇒
  let z0 : `bool ⇒ x.car in
  let z1 : `bool ⇒ x.cdr in
  < z0, z1 >


let testing [x : `(bool [1=1 tt])] : singleton `bool `tt ⇒
  x

let hset [A : type] : type =>
  (x : A)
  (y : A)
  (p : Path A x y)
  (q : Path A x y)
  → Path (Path A x y) p q

let hset/exponential-ideal
  [A : type]
  [B : type]
  [hset/B : hset B]
  : hset (A → B)
  =>
  λ f g α β i j x →
    let foo => hset/B _ _ (λ k → `(@ α k) x) (λ k → `(@ β k) x) in
    `(@ (@ foo i) j)


