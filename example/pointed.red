import bool
import isotoequiv

let ptype : type^1 = (A : type) × A
 
let pmap (pA,pB : ptype) : type^1 =
  (f : (pA.0) → (pB.0)) × Path _ (f (pA.1)) (pB.1)

let p→ (pA,pB : ptype) : ptype^1 = < pmap pA pB, λ a → pB.1 , λ i → pB.1 >

let pequiv (pA,pB : ptype) : type^1 =
  (f : pmap pA pB) × IsEquiv (pA.0) (pB.0) (f.0)

let pbool : ptype = < bool , ff >

; B is pmap pbool pA
; e is fwd = <e1,p>
; inv is bwd

;    <i> (\(b : bool) -> indBool (\(b : bool) -> Path A.1 ((inv (e1 f)).1 b) (f.1 b))
;                                (<i> f.2 @ -i)
;                                (<_> f.1 true) b @ i,
;          <j> f.2 @ (-i \/ j))

let pf (pA : ptype) : pequiv^1 (p→ pbool pA) pA =
  let fwd : pmap^1 (p→ pbool pA) pA = <λ f → f.0 tt , λ i → pA.1> in
  let bwd : (pA.0) → (pmap pbool pA) = λ a →
    < λ b → elim b [
            | tt ⇒ a
            | ff ⇒ pA.1
            ]
    , λ i → pA.1 > in
  let bwdfwd : (f : pmap pbool pA) → Path _ (bwd (fwd.0 f)) f = λ f i → 
    ?{
       <λ b → elim b [
                     | tt ⇒ f.0 tt
                     | ff ⇒ symm _ (f.1) i
                     ]
       ,λ j → ?cfhm>
     }
  in
  <fwd,(Iso/Equiv^1 _ _ <fwd.0,bwd,λ a i → a,bwdfwd>).1>
