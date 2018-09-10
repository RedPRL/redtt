import path

let connection/or
 (A : type)
 (p : dim → A)
 : [i j] A [
   | j=0 → p i
   | i=0 → p j
   | j=1 | i=1 → p 1
   | i=j → p i
   ]
 =
 λ i j →
  ; this is an example of something that is much nicer here than in redprl.
  ; we can define using line types all the faces of the composition at once.
  ; definitional equivalence kicks in to make this work.
  let face (l k : dim) : A =
    comp 1 l (p 1) [
    | k=1 → refl
    | k=0 → p
    ]
  in
  comp 1 0 (p 1) [
  | i=0 → face j
  | j=0 → face i
  | i=1 | j=1 → refl
  | i=j → face i
  ]

let connection/and
 (A : type)
 (p : dim → A)
 : [i j] A [
   | j=0 | i=0 → p 0
   | j=1 → p i
   | i=1 → p j
   | i=j → p i
   ]
 =
 λ i j →
   let face (l k : dim) : A =
     comp 0 l (p 0) [
     | k=0 → refl
     | k=1 → p
     ]
   in
   comp 0 1 (p 0) [
   | i=0 | j=0 → refl
   | i=1 → face j
   | j=1 → face i
   | i=j → face i
   ]

let connection/both
  (A : type)
  (p : dim → A) (q : [k] A [k=0 → p 1])
  : [i j] A [
    | i=0 → p j
    | i=1 → q j
    | j=0 → p i
    | j=1 → q i
    ]
  =
  λ i j →
    let pface (m k : dim) : A =
      comp 1 m (p k) [
      | k=0 → refl
      | k=1 → p
      ]
    in
    let qface (m k : dim) : A =
      comp 0 m (p k) [
      | k=0 → refl
      | k=1 → q
      ]
    in
    comp 0 1 (p 0) [
    | i=0 → pface j
    | i=1 → qface j
    | j=0 → pface i
    | j=1 → qface i
    ]

let weak-connection/or
 (A : type)
 (p : dim → A)
 : [i j] A [
   | i=0 → p j
   | j=0 → p i
   | i=1 | j=1 → p 1
   ]
 =
 λ i j →
  let face (l k : dim) : A =
    comp 1 l (p 1) [
    | k=1 → refl
    | k=0 → p
    ]
  in
  comp 1 0 (p 1) [
  | i=0 → face j
  | j=0 → face i
  | i=1 | j=1 → refl
  ]

let weak-connection/and
 (A : type)
 (p : dim → A)
 : [i j] A [
   | i=0 | j=0 → p 0
   | i=1 → p j
   | j=1 → p i
   ]
 =
 λ i j →
   let face (l k : dim) : A =
     comp 0 l (p 0) [
     | k=0 → refl
     | k=1 → p
     ]
   in
   comp 0 1 (p 0) [
   | i=0 | j=0 → refl
   | i=1 → face j
   | j=1 → face i
   ]
