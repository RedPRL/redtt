import path

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
      | k=1 ⇒ auto
      | k=0 ⇒ p
      ]
  in
  comp 1 0 (p 1) [
  | i=0 ⇒ face j
  | i=1 ⇒ face 1
  | j=0 ⇒ face i
  | j=1 ⇒ face 1
  | i=j ⇒ face i
  ]

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
       | k=0 ⇒ auto
       | k=1 ⇒ p
       ]
   in
   comp 0 1 (p 0) [
   | i=0 ⇒ face 0
   | i=1 ⇒ face j
   | j=0 ⇒ face 0
   | j=1 ⇒ face i
   | i=j ⇒ face i
   ]


