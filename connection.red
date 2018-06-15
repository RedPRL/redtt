import path

let singleton (A : type) (M : A) : `(U pre 0) =
  `(A [0=0 M])

let connection/or
 (A : type)
 (a : A)
 (b : A)
 (p : Path A a b)
 : `(# <i j> A [j=0 (@ p i)] [i=0 (@ p j)] [j=1 b] [i=1 b])
 =
 λ i j →
  ; this is an example of something that is much nicer here than in redprl and yacctt.
  ; we can define using line types all the faces of the composition at once.
  ; definitional equivalence kicks in to make this work.
  let face : `(# <_> (# <_>  A)) =
    λ l k →
      comp 0 l (p k) with
      | k=1 ⇒ λ _ → b
      | k=0 ⇒ p
      end
  in
  comp 1 0 b with
  | i=0 ⇒ face j
  | i=1 ⇒ face 1
  | j=0 ⇒ face i
  | j=1 ⇒ face 1
  | i=j ⇒ face i
  end

; an example of using the singleton type to establish an exact equality
let connection/or/diagonal
 (A : type)
 (a : A)
 (b : A)
 (p : Path A a b)
 : singleton (Path A a b) p
 =
 λ i →
   connection/or _ a b p i i

let connection/and
 (A : type)
 (a : A)
 (b : A)
 (p : Path A a b)
 : `(# <i j> A [j=0 a] [i=0 a] [j=1 (@ p i)] [i=1 (@ p j)])
 =
 λ i j →
   let face : `(# <_> (# <_> A)) =
     λ l k →
       comp 1 l (p k) with
       | k=0 ⇒ λ _ → a
       | k=1 ⇒ p
       end
   in
   comp 0 1 a with
   | i=0 ⇒ face 0
   | i=1 ⇒ face j
   | j=0 ⇒ face 0
   | j=1 ⇒ face i
   | i=j ⇒ face i
   end


