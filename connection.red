import path

let singleton (A : type) (M : A) : type pre =
  restrict A [
  | 0=0 ⇒ M
  ]

let connection/or
 (A : type)
 (p : dim → A)
 : [i j] A [
   | j=0 ⇒ p i
   | i=0 ⇒ p j
   | j=1 ⇒ p 1
   | i=1 ⇒ p 1
   ]
 =
 λ i j →
  ; this is an example of something that is much nicer here than in redprl.
  ; we can define using line types all the faces of the composition at once.
  ; definitional equivalence kicks in to make this work.
  let face : dim → dim → A =
    λ l k →
      comp 0 l (p k) [
      | k=1 ⇒ λ _ → p 1
      | k=0 ⇒ λ m → p m
      ]
  in
  comp 1 0 (p 1) [
  | i=0 ⇒ λ k → face j k
  | i=1 ⇒ λ k → face 1 k
  | j=0 ⇒ λ k → face i k
  | j=1 ⇒ λ k → face 1 k
  | i=j ⇒ λ k → face i k
  ]

; an example of using the singleton type to establish an exact equality
let connection/or/diagonal
 (A : type)
 (p : dim → A)
 : singleton _ p
 =
 λ i →
   connection/or _ p i i

let connection/and
 (A : type)
 (p : dim → A)
 : [i j] A [
   | j=0 ⇒ p 0
   | i=0 ⇒ p 0
   | j=1 ⇒ p i
   | i=1 ⇒ p j
   ]
 =
 λ i j →
   let face : dim → dim → A =
     λ l k →
       comp 1 l (p k) [
       | k=0 ⇒ λ _ → p 0
       | k=1 ⇒ λ m → p m
       ]
   in
   comp 0 1 (p 0) [
   | i=0 ⇒ λ k → face 0 k
   | i=1 ⇒ λ k → face j k
   | j=0 ⇒ λ k → face 0 k
   | j=1 ⇒ λ k → face i k
   | i=j ⇒ λ k → face i k
   ]


