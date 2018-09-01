import bool
import isotoequiv

let ptype : type^1 = (A : type) × A

let pmap (pA,pB : ptype) : type =
  (f : (pA.0) → (pB.0)) × Path _ (f (pA.1)) (pB.1)

let p→ (pA,pB : ptype) : ptype = < pmap pA pB, λ a → pB.1 , λ i → pB.1 >

let pequiv (pA,pB : ptype) : type =
  (f : pmap pA pB) × IsEquiv (pA.0) (pB.0) (f.0)

let pbool : ptype = < bool , ff >

let pf (pA : ptype) : pequiv (p→ pbool pA) pA =
  let fwd : pmap (p→ pbool pA) pA =
    <λ f → f.0 tt , λ i → pA.1>
  in
  let bwd : (pA.0) → (pmap pbool pA) = λ a →
    < λ b → elim b [
            | tt ⇒ a
            | ff ⇒ pA.1
            ]
    , λ i → pA.1 >
  in
  let bwdfwd : (f : pmap pbool pA) → Path (pmap pbool pA) (bwd (fwd.0 f)) f =
    λ f →
      let bwdfwd/pt : (i, j : dim) → pA.0
        =
        λ i j →
          comp 1 j (pA.1) [
          | i=0 ⇒ refl
          | i=1 ⇒ f.1
          ]
      in
      let bwdfwd/map : (b : bool) → Path (pA.0) ((bwd (fwd.0 f)).0 b) (f.0 b) =
        λ b →
          elim b [
          | tt ⇒ refl
          | ff ⇒ λ i → bwdfwd/pt i 0
          ]
      in
      λ i →
        < λ b → bwdfwd/map b i
        , λ j → bwdfwd/pt i j
        >
  in
  <fwd, (Iso/Equiv _ _ <fwd.0, bwd, λ a i → a, bwdfwd>).1>
