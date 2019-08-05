import prelude.path

def connection/or
  (A : type)
  (p : 𝕀 → A)
  : [i j] A [
    | j=0 | i=j → p i
    | j=1 | i=1 → p 1
    | i=0 → p j
    ]
  =
  λ i j →
  /- this is an example of something that is much nicer here than in redprl.
     we can define using line types all the faces of the composition at once.
     definitional equivalence kicks in to make this work.
  -/
  let face (l k : 𝕀) : A =
    comp 1 l (p 1) [
    | k=1 → refl
    | k=0 → p
    ]
  in
  comp 1 0 (p 1) [
  | i=0 → face j
  | j=0 | i=j → face i
  | i=1 | j=1 → refl
  ]

def connection/and
  (A : type)
  (p : 𝕀 → A)
  : [i j] A [
    | j=0 | i=0 → p 0
    | j=1 | i=j → p i
    | i=1 → p j
    ]
  =
  λ i j →
  let face (l k : 𝕀) : A =
    comp 0 l (p 0) [
    | k=0 → refl
    | k=1 → p
    ]
  in
  comp 0 1 (p 0) [
  | i=0 | j=0 → refl
  | i=1 → face j
  | j=1 | i=j → face i
  ]

def connection/both
  (A : type)
  (p : 𝕀 → A) (q : [k] A [k=0 → p 1])
  : [i j] A [
    | i=0 → p j
    | i=1 → q j
    | j=0 → p i
    | j=1 → q i
    ]
  =
  λ i j →
  let pface (m k : 𝕀) : A =
    comp 1 m (p 1) [
    | k=0 → refl
    | k=1 → p
    ]
  in
  let qface (m k : 𝕀) : A =
    comp 0 m (p 1) [
    | k=0 → refl
    | k=1 → q
    ]
  in
  comp 0 1 (p 1) [
  | i=0 → pface j
  | i=1 → qface j
  | j=0 → pface i
  | j=1 → qface i
  ]

def weak-connection/or
  (A : type)
  (p : 𝕀 → A)
  : [i j] A [
    | i=0 → p j
    | j=0 → p i
    | i=1 | j=1 → p 1
    ]
  =
  λ i j →
  let face (l k : 𝕀) : A =
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

def weak-connection/and
  (A : type)
  (p : 𝕀 → A)
  : [i j] A [
    | i=0 | j=0 → p 0
    | i=1 → p j
    | j=1 → p i
    ]
  =
  λ i j →
  let face (l k : 𝕀) : A =
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

def weak-connection/or-not -- i \/ ~j
  (A : type)
  (p : 𝕀 → A)
  : [i j] A [
  | i=0 → symm A p j
  | i=1 | j=0 → p 1
  | j=1 → p i
  ]
  =
  λ i j →
  comp 0 1 (p 0) [
  | j=0 | i=1 → p
  | j=1 k → connection/and A p i k
  ]


