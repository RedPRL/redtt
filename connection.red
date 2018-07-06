import path

let singleton (A : type) (M : A) : `(U pre 0) =
  restrict A with
  | 0=0 ⇒ M
  end

let connection/or
 (A : type)
 (a : A)
 (b : A)
 (p : Path A a b)
 : [i j] A with
   | j=0 ⇒ p i
   | i=0 ⇒ p j
   | j=1 ⇒ b
   | i=1 ⇒ b
   end
 =
 λ i j →
  ; this is an example of something that is much nicer here than in redprl.
  ; we can define using line types all the faces of the composition at once.
  ; definitional equivalence kicks in to make this work.
  let face : Line (Line A) =
    λ l k →
      comp 0 l (p k) with
      | k=1 ⇒ λ _ → b
      | k=0 ⇒ λ m → p m
      end
  in
  comp 1 0 b with
  | i=0 ⇒ λ k → face j k
  | i=1 ⇒ λ k → face 1 k
  | j=0 ⇒ λ k → face i k
  | j=1 ⇒ λ k → face 1 k
  | i=j ⇒ λ k → face i k
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
 : [i j] A with
   | j=0 ⇒ a
   | i=0 ⇒ a
   | j=1 ⇒ p i
   | i=1 ⇒ p j
   end
 =
 λ i j →
   let face : Line (Line A) =
     λ l k →
       comp 1 l (p k) with
       | k=0 ⇒ λ _ → a
       | k=1 ⇒ λ m → p m
       end
   in
   comp 0 1 a with
   | i=0 ⇒ λ k → face 0 k
   | i=1 ⇒ λ k → face j k
   | j=0 ⇒ λ k → face 0 k
   | j=1 ⇒ λ k → face i k
   | i=j ⇒ λ k → face i k
   end


